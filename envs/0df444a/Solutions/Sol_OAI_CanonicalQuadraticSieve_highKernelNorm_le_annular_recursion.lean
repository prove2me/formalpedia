-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.highKernelNorm_le_annular_recursion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:50:51.357749+00:00
-- url     : https://prove2.me/submissions/5cc4264e-b786-48ea-a8ba-9dea709299c0

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
import Theorems.Thm_OAI_CanonicalQuadraticSieve_highKernelNorm_le_dyadic_shells
import Theorems.Thm_OAI_CanonicalQuadraticSieve_highKernelShellNorm_le_annularThirdNorm

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical
open scoped SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K G : ℝ) (lengthScale : ℕ)
    (hML : M ≤ (2 : ℝ) ^ lengthScale) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 * ∑ j ∈ Finset.range (lengthScale + 1),
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm ((2 : ℝ) ^ j) N K D) +
        highKernelNorm (2 * (2 : ℝ) ^ j) (N / G) K *
          (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply (highKernelNorm_le_dyadic_shells M N K lengthScale hML).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j hj => highKernelShellNorm_le_annularThirdNorm
    ((2 : ℝ) ^ j) N K G (by positivity) hN hG ε hε)
end OAI.CanonicalQuadraticSieve
