# Chapter 2: Kernelization

> Kernelization is a systematic approach to study polynomial-time preprocessing algorithms. It is an important tool in the design of parameterized algorithms. In this chapter we explain basic kernelization techniques such as crown decomposition, the expansion lemma, the sunower lemma, and linear programming. We illustrate these techniques by obtaining kernels for Vertex Cover, Feedback Arc Set in Tournaments, Edge Clique Cover, Maximum Satisfiability, and d-Hitting Set.

Preprocessing (data reduction or kernelization) is used universally in almost every practical computer implementation that aims to deal with an NPhard problem. The goal of a preprocessing subroutine is to solve eciently the easy parts of a problem instance and reduce it (shrink it) to its computationally dicult core structure (the problem kernel of the instance). In other words, the idea of this method is to reduce (but not necessarily solve) the given problem instance to an equivalent smaller sized instance in time polynomial in the input size. A slower exact algorithm can then be run on this smaller instance.

How can we measure the effectiveness of such a preprocessing subroutine? Suppose we dene a useful preprocessing algorithm as one that runs in polynomial time and replaces an instance I with an equivalent instance that is at least one bit smaller. Then the existence of such an algorithm for an NP-hard problem would imply P= NP, making it unlikely that such an algorithm can be found. For a long time, there was no other suggestion for a formal denition of useful preprocessing, leaving the mathematical analysis of polynomial-time preprocessing algorithms largely neglected. But in the language of parameterized complexity, we can formulate a denition of useful preprocessing by demanding that large instances with a small parameter should be shrunk, while instances that are small compared to their parameter do not have to be processed further. These ideas open up the lost continent of polynomial-time algorithms called kernelization.

In this chapter we illustrate some commonly used techniques to design kernelization algorithms through concrete examples. The next section, Section 2.1, provides formal denitions. In Section 2.2 we give kernelization algorithms based on so-called natural reduction rules. Section 2.3 introduces the concepts of crown decomposition and the expansion lemma, and illustrates it on Maximum Satisfiability. Section 2.5 studies tools based on linear programming and gives a kernel for Vertex Cover. Finally, we study the sunower lemma in Section 2.6 and use it to obtain a polynomial kernel for d-Hitting Set.

## 2.1 Formal definitions

We now turn to the formal denition that captures the notion of kernelization. A data reduction rule, or simply, reduction rule, for a parameterized problem Q is a function φ: Σ∗×N →Σ∗×N that maps an instance (I,k) of Q to an equivalent instance (I′,k′) of Q such that φ is computable in time polynomial in |I|and k. We say that two instances of Q are equivalent if (I,k) ∈Qif and only if (I′,k′) ∈Q; this property of the reduction rule φ, that it translates an instance to an equivalent one, is sometimes referred to as the safeness or soundness of the reduction rule. In this book, we stick to the phrases: a rule is safe and the safeness of a reduction rule.

The general idea is to design a preprocessing algorithm that consecutively applies various data reduction rules in order to shrink the instance size as much as possible. Thus, such a preprocessing algorithm takes as input an instance (I,k) ∈Σ∗×N of Q, works in polynomial time, and returns an equivalent instance (I′,k′) of Q. In order to formalize the requirement that the output instance has to be small, we apply the main principle of Parameterized Complexity: The complexity is measured in terms of the parameter. Consequently, the output size of a preprocessing algorithm A is a function size A: N →N ∪{∞}dened as follows:
sizeA(k) = sup{|I′|+ k′ : (I′,k′) = A(I,k), I ∈Σ∗}.
In other words, we look at all possible instances of Qwith a xed parameter k, and measure the supremum of the sizes of the output of Aon these instances. Note that this supremum may be innite; this happens when we do not have any bound on the size of A(I,k) in terms of the input parameter k only. Kernelization algorithms are exactly these preprocessing algorithms whose output size is nite and bounded by a computable function of the parameter.

**Denition 2.1 (Kernelization, kernel).** A kernelization algorithm, or simply a kernel, for a parameterized problem Qis an algorithm Athat, given an instance (I,k) of Q, works in polynomial time and returns an equivalent instance (I′,k′) of Q. Moreover, we require that sizeA(k) ≤g(k) for some computable function g: N →N.

The size requirement in this denition can be reformulated as follows: There exists a computable function g(·) such that whenever (I′,k′) is the output for an instance (I,k), then it holds that |I′|+ k′≤g(k). If the upper bound g(·) is a polynomial (linear) function of the parameter, then we say that Qadmits a polynomial (linear) kernel . We often abuse the notation and call the output of a kernelization algorithm the reduced equivalent instance, also a kernel.

In the course of this chapter, we will often encounter a situation when in some boundary cases we are able to completely resolve the considered problem instance, that is, correctly decide whether it is a yes-instance or a no-instance. Hence, for clarity, we allow the reductions (and, consequently, the kernelization algorithm) to return a yes/no answer instead of a reduced instance. Formally, to t into the introduced denition of a kernel, in such cases the kernelization algorithm should instead return a constant-size trivial yes-instance or no-instance. Note that such instances exist for every parameterized language except for the empty one and its complement, and can be therefore hardcoded into the kernelization algorithm.

Recall that, given an instance (I,k) of Q, the size of the kernel is dened as the number of bits needed to encode the reduced equivalent instance I′ plus the parameter value k′. However, when dealing with problems on graphs, hypergraphs, or formulas, often we would like to emphasize other aspects of output instances. For example, for a graph problem Q, we could say that Q admits a kernel with O(k3) vertices and O(k5) edges to emphasize the upper bound on the number of vertices and edges in the output instances. Similarly, for a problem dened on formulas, we could say that the problem admits a kernel with O(k) variables.

It is important to mention here that the early denitions of kernelization required that k′≤k. On an intuitive level this makes sense, as the parameter k measures the complexity of the problem thus the larger the k, the harder the problem. This requirement was subsequently relaxed, notably in the context of lower bounds. An advantage of the more liberal notion of kernelization is that it is robust with respect to polynomial transformations of the kernel. However, it limits the connection with practical preprocessing. All the kernels mentioned in this chapter respect the fact that the output parameter is at most the input parameter, that is, k′≤k.

While usually in Computer Science we measure the eciency of an algorithm by estimating its running time, the central measure of the eciency of a kernelization algorithm is a bound on its output size. Although the actual running time of a kernelization algorithm is often very important for practical applications, in theory a kernelization algorithm is only required to run in polynomial time.

If we have a kernelization algorithm for a problem for which there is some algorithm (with any running time) to decide whether (I,k) is a yes-instance, then clearly the problem is FPT, as the size of the reduced instance I is simply a function of k (and independent of the input size n). However, a surprising result is that the converse is also true.

**Lemma 2.2.** If a parameterized problem Q is FPT then it admits a kernelization algorithm.

Proof. Since Q is FPT, there is an algorithm A deciding if (I,k) ∈Q in time f(k) ·|I|c for some computable function f and a constant c. We obtain a kernelization algorithm for Qas follows. Given an input (I,k), the kernelization algorithm runs Aon (I,k), for at most |I|c+1 steps. If it terminates with an answer, use that answer to return either that (I,k) is a yes-instance or that it is a no-instance. If Adoes not terminate within |I|c+1 steps, then return (I,k) itself as the output of the kernelization algorithm. Observe that since Adid not terminate in |I|c+1 steps, we have that f(k) ·|I|c > |I|c+1, and thus |I|<f(k). Consequently, we have |I|+ k ≤f(k) + k, and we obtain a kernel of size at most f(k) + k; note that this upper bound is computable as f(k) is a computable function.

Lemma 2.2 implies that a decidable problem admits a kernel if and only if it is fixed-parameter tractable. Thus, in a sense, kernelization can be another way of defining fixed-parameter tractability.

However, kernels obtained by this theoretical result are usually of exponential (or even worse) size, while problem-specic data reduction rules often achieve quadratic (g(k) = O(k2)) or even linear-size (g(k) = O(k)) kernels. So a natural question for any concrete FPT problem is whether it admits a problem kernel that is bounded by a polynomial function of the parameter (g(k) = kO(1)). In this chapter we give polynomial kernels for several problems using some elementary methods. In Chapter 9, we give more advanced methods for obtaining kernels.

## 2.2 Some simple kernels

In this section we give kernelization algorithms for Vertex Cover and Feedback Arc Set in Tournaments (FAST) based on a few natural reduction rules.

### 2.2.1 Vertex Cover

Let G be a graph and S ⊆V(G). The set S is called a vertex cover if for every edge of G at least one of its endpoints is in S. In other words, the graph G−S contains no edges and thus V(G) \S is an independent set. In the Vertex Cover problem, we are given a graph Gand a positive integer k as input, and the objective is to check whether there exists a vertex cover of size at most k.

The first reduction rule is based on the following simple observation. For a given instance (G,k) of Vertex Cover, if the graph G has an isolated vertex, then this vertex does not cover any edge and thus its removal does not change the solution. This shows that the following rule is safe.

**Reduction VC.1.** If G contains an isolated vertex v, delete v from G. The new instance is (G−v,k). The second rule is based on the following natural observation:

If G contains a vertex v of degree more than k, then v should be in every vertex cover of size at most k.

Indeed, this is because if v is not in a vertex cover, then we need at least k+ 1 vertices to cover edges incident to v. Thus our second rule is the following.

**Reduction VC.2.** If there is a vertex v of degree at least k+ 1, then delete v (and its incident edges) from G and decrement the parameter k by 1. The new instance is (G−v,k−1).

Observe that exhaustive application of reductions VC.1 and VC.2 completely removes the vertices of degree 0 and degree at least k+ 1. The next step is the following observation.

If a graph has maximum degree d, then a set of k vertices can cover at most kd edges.

This leads us to the following lemma.

**Lemma 2.3.** If (G,k) is a yes-instance and none of the reduction rules VC.1, VC.2 is applicable to G, then |V(G)|≤k2 + k and |E(G)|≤k2.

Proof. Because we cannot apply Reductions VC.1 anymore on G, G has no isolated vertices. Thus for every vertex cover S of G, every vertex of G−S should be adjacent to some vertex from S. Since we cannot apply Reductions VC.2, every vertex of G has degree at most k. It follows that |V(G−S)|≤k|S|and hence |V(G)|≤(k + 1)|S|. Since (G,k) is a yesinstance, there is a vertex cover S of size at most k, so |V(G)|≤(k+ 1)k. Also every edge of Gis covered by some vertex from a vertex cover and every vertex can cover at most k edges. Hence if Ghas more than k2 edges, this is again a no-instance.

Lemma 2.3 allows us to claim the nal reduction rule that explicitly bounds the size of the kernel.

**Reduction VC.3.** Let (G,k) be an input instance such that Reductions VC.1 and VC.2 are not applicable to (G,k). If k<0 and G has more than k2 + k vertices, or more than k2 edges, then conclude that we are dealing with a no-instance.

Finally, we remark that all reduction rules are trivially applicable in linear time. Thus, we obtain the following theorem.

**Theorem 2.4.** Vertex Cover admits a kernel with O(k2) vertices and O(k2) edges.
