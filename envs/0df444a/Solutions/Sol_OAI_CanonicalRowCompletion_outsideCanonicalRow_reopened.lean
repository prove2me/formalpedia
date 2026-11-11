-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.outsideCanonicalRow_reopened
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:05:15.856876+00:00
-- url     : https://prove2.me/submissions/94c6748f-398f-49d2-9631-e5f09b6aef64

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_SupportBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation
import Theorems.Thm_OAI_CanonicalRowCompletion_large_cube_sum_finite
import Theorems.Thm_OAI_CanonicalRowCompletion_inner_completed_sum
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeWeight_row_factor
import Theorems.Thm_OAI_CanonicalRowCompletion_excludedGenerator_mem
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideCanonicalRow_cube_split
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideCanonicalRow_eq_global
import Theorems.Thm_OAI_CompletedGauss_norm_at_least_one


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
namespace OAI.CanonicalRowCompletion
theorem _root_.solution (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B * cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) B *
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) * idealRowHom z B^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm B:ℝ)^3) := by
  rw [outsideCanonicalRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hB0 : B≠0 := outsideIdealsUpTo_ne_bot S D B hB
  have hN := norm_at_least_one B hB0
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := by positivity
  have hYX : X/(Ideal.absNorm B:ℝ)^3 ≤ X :=
    div_le_self hX.le (one_le_pow₀ hN)
  have hDY : b*(X/(Ideal.absNorm B:ℝ)^3) ≤ D :=
    (mul_le_mul_of_nonneg_left hYX hb).trans hD
  rw [inner_completed_sum _ W X hX B hB0]
  rw [←outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b
    (X/(Ideal.absNorm B:ℝ)^3) hY hW hDY]
  rw [cubeWeight_row_factor]
  ring
end OAI.CanonicalRowCompletion
