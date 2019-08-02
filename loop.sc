import $ivy.{
  `com.lihaoyi::requests:0.2.0`,
  `com.lihaoyi::upickle:0.7.5`
}


// ================================================================
//
//   type synonyms and record types to make things easier
//
// ==============================================================


type Vertex = String
type VertexList = List[Vertex]


case class Edge(start: Vertex, stop: Vertex, weight: Double)
type EdgeList = List[Edge]


type DistanceMap = Map[Vertex, Double]
type PredecessorMap = Map[Vertex, Option[Vertex]]


// ================================================================
//
//                     Utils
//
// ==============================================================


// run-time complexity is about O(n)
// Doc: This prints out the path 
def parentMappingHelper(ps: PredecessorMap, source: Vertex, t: VertexList = List()): VertexList = {
     if (t contains source) {
         t :+ source
     } else {
        ps.get(source).flatten match {
           case Some(x) => parentMappingHelper(ps,x, t :+ source)
           case _ => t :+ source
     }}  
}


// worst run-time complexity is about O(n^2)
def transformPredecessorMap(ps: PredecessorMap):Map[Vertex, VertexList] = {
  ps.keys.map {(x) => (x,parentMappingHelper(ps,x).reverse)} .toMap 
}


// ================================================================
//
//                     Bellman-Ford
//
// ==============================================================


// runtime complecity is about k*O(1) which for the sake of analysis can be dumbed down to  O(1)
def relax(edge: Edge, ds: Map[Vertex,Double]): Option[Double] = {
  edge match {
   case Edge(s,e,w) => for { 
                        du <- ds get s
                        dv <- ds get e
                        x <- Some(du + w)
                        r <-  if (du != Double.PositiveInfinity && dv > x){
                               Option(x)} else { None }}
                       yield r}}


// runtime complexity is O(E) where E is the number of edges
def relaxEdgeList( es: EdgeList, ds: DistanceMap , ps: PredecessorMap) : (DistanceMap, PredecessorMap) = { 

    es.foldLeft((ds,ps)) { (acc,edge) => { relax(edge,acc._1) match { case Some(x) =>  (acc._1 + (edge.stop -> x), acc._2 + (edge.stop -> Some(edge.start)))  
                                                                      case        _ => acc }}}} 



//  time complexity of this is O(E)  
def negativeCycleCheck(es:EdgeList, ds: DistanceMap) : Boolean = {

   es.map {(edge) => { relax(edge, ds) match { case Some(_) => true 
                                               case       _ => false}}} 
      . foldLeft(false) (_ || _)

}


// O(n) + O(n) + O(V*E) + O(2*E) ~~ O(V*E)
def bellmanFord(vs:VertexList , es: EdgeList, start: Vertex) 
: (Boolean, DistanceMap, PredecessorMap) = {

   // O(n) for now, make this more performant
   val ds: DistanceMap = vs.map {x => (x, Double.PositiveInfinity)} . toMap . + (start -> 0.0) 
   val ps: PredecessorMap = vs.map {x => (x, None)} . toMap 

   val acc =  (0 to (vs.length-1)). foldLeft ((ds,ps)) {(acc, _) => relaxEdgeList(es,acc._1,acc._2)} 

   if (negativeCycleCheck(es,acc._1)) {
     (false, acc._1, acc._2)
   } else {
     (true, acc._1, acc._2)
   } 
     
}


// ================================================================
//
//                     Arbitage detector
//
// ==============================================================


def arbitageDetection(es:EdgeList):Option[VertexList] = {

  val vertexList = es.map(x => List(x.start,x.stop)).flatten.toSet.toList

  val r = bellmanFord(vertexList, es, scala.util.Random.shuffle(vertexList).head)

  if (r._1 == false) {
    val acc = relaxEdgeList(es,r._2,r._3)
    val source = (r._2.toSet diff acc._1.toSet).head._1
    Some(parentMappingHelper(acc._2, source))
  } else {
    None
  }
}


// ================================================================
//
//                     Test runs and main
//
// ==============================================================



@doc("Test for graph example found here https://www.geeksforgeeks.org/bellman-ford-algorithm-dp-23/")
@main
def test1():Unit = {
   val vs:VertexList = List("0","1","2","3","4")

   val es:EdgeList = List(Edge("0","1",-1), Edge("0","2",4), Edge("1","2",3), Edge("1","3",2), 
                          Edge("1","4",2), Edge("3","2",5), Edge("3","1",1), Edge("4","3",-3))

  
   val bfResult = bellmanFord(vs,es,"0")


   val expectedResult = Map("4" -> List("0", "1", "4"), "1" -> List("0", "1"), "0" -> List("0"), "2" -> List("0", "1", "2"), "3" -> List("0", "1", "4", "3"))

   assert((transformPredecessorMap(bfResult._3).toSet diff expectedResult.toSet).toList == List())

}


@doc("Sample profit run for pricenomics example found here  https://priceonomics.com/jobs/puzzle/")
@main
def test2():Unit = {
  // val vs2:VertexList = List("usd","eur","jpy","btc")


  val es2:EdgeList = List( ("usd",List(("eur", 0.7779),("jpy", 102.4590),("btc",0.0083)))
                       , ("eur",List(("usd", 1.2851),("jpy", 131.7110),("btc",0.01125)))
                       , ("jpy",List(("usd", 0.0098),("eur", 0.0075),("btc",0.0000811)))
                       , ("btc",List(("usd", 115.65),("eur", 88.8499),("jpy",12325.44))) 
                       )
                    . map { x => { x._2.map { y => Edge(x._1, y._1, -scala.math.log(y._2))}}}
                    . flatten

  assert(arbitageDetection(es2).getOrElse(List()) sameElements  List("usd", "jpy", "btc", "eur", "usd"))
}


@doc("Actual runs with data from pricenomics")
@main
def run():Unit = {
   val url = "http://fx.priceonomics.com/v1/rates/"

   val responseAsEdgeList = upickle
                         .default
                         .read[Map[String,Double]](requests.get(url).text) 
                         .toList
                         .map {x => { val a = x._1.split("_").map { _.toLowerCase}
                                      Edge(a(0), a(1), x._2)}}
                         .filter { x => x.start != x.stop}

   arbitageDetection(responseAsEdgeList) match {
     case Some(x) => println("Arbitage loop detected " ++ x)
     case None => println("No arbitage loop detected !!!")
   }
   
}

