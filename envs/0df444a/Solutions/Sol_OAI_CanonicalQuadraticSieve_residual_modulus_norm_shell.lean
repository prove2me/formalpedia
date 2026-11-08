-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.residual_modulus_norm_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:05:13.447184+00:00
-- url     : https://prove2.me/submissions/f17ee6dd-eca8-4b05-8bdf-6ac9694214a2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_in_shell
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_idealQuotient
import Theorems.Thm_OAI_CanonicalQuadraticSieve_primaryGenerator_admissible
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_norm_sq


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
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (I J D : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (N : ℝ) (hN : 0 < N)
    (hIs : N / 2 < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (hJs : N / 2 < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ N) :
    (N / (Ideal.absNorm D : ℝ)) / 2 <
      ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ∧
    ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ≤
      N / (Ideal.absNorm D : ℝ) := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have hQ := admissible_idealQuotient hI hDI
  have hT := admissible_idealQuotient hJ hDJ
  have hqi := idealQuotient_in_shell I D hI hDI N hIs.1 hIs.2
  have hqj := idealQuotient_in_shell J D hJ hDJ N hJs.1 hJs.2
  let X := N / (Ideal.absNorm D : ℝ)
  have hX : 0 < X := div_pos hN hDN
  have hn : ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ^ 2 =
      (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) := by
    rw [map_mul, norm_mul, mul_pow,
      primaryGenerator_norm_sq _ (primaryGenerator_admissible _ hQ),
      primaryGenerator_norm_sq _ (primaryGenerator_admissible _ hT)]
  have hlo : (X / 2) * (X / 2) <
      (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) :=
    mul_lt_mul hqi.1 hqj.1.le (by positivity) (by positivity)
  have hhi : (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) ≤ X * X :=
    mul_le_mul hqi.2 hqj.2 (Nat.cast_nonneg _) hX.le
  have hnorm := norm_nonneg (eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J)))
  constructor
  · nlinarith
  · nlinarith
end OAI.CanonicalQuadraticSieve
