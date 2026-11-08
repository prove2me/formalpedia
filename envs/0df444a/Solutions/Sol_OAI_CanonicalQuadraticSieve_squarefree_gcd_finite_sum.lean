-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.squarefree_gcd_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:28:54.874214+00:00
-- url     : https://prove2.me/submissions/720d2516-9312-4e81-be9b-b32522f88147

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_LogDensity
import Theorems.Thm_OAI_CanonicalQuadraticSieve_squarefree_cutoff_summable
import Theorems.Thm_OAI_CanonicalQuadraticSieve_coprime_squarefree_cutoff
import Theorems.Thm_OAI_CanonicalQuadraticSieve_tsum_squarefree_norm_cutoff


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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (G : Ideal O) (hG : Squarefree G) (K : ℝ) (f : Ideal O → ℂ) :
    (∑ B : squarefreeIdealRange K, f B.val) =
      ∑ D : idealDivisors G, ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0 := by
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs := (squarefreeGcdEquiv G hG).symm.summable_iff.mpr (squarefree_cutoff_summable K f)
  have he := ((squarefreeGcdEquiv G hG).symm.tsum_eq F).symm
  calc
    _ = ∑' B : {B : Ideal O // Squarefree B}, F B := (tsum_squarefree_norm_cutoff K f).symm
    _ = ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm p) := he
    _ = ∑' D : idealDivisors G, ∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm (D, H)) := hs.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro D _
      change (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0) = _
      exact coprime_squarefree_cutoff G D.val
        (ne_zero_of_dvd_ne_zero hG.ne_zero ((mem_idealDivisors hG.ne_zero).mp D.property)) K f
end OAI.CanonicalQuadraticSieve
