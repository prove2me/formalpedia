-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.outside_separated_cube_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:15:12.261559+00:00
-- url     : https://prove2.me/submissions/e95dcae1-64b9-41d3-a4ee-83163534a1ba

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
import Theorems.Thm_OAI_CanonicalCubeSeparation_separatedCubeCoefficient_bound
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIdeal_ne_zero
import Theorems.Thm_OAI_CanonicalRowCompletion_reopenedCubeCoefficient_small_power
import Theorems.Thm_OAI_CanonicalRowCompletion_rowTwist_norm


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
open CanonicalCubeSeparation
namespace OAI.CanonicalRowCompletion
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m f : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
      (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ),
      0 < B →
      B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) →
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B →
      ‖separatedCubeCoefficient
        (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
          (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
        (fun u => (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u) : ℝ))
        B ξ v‖ ≤ C*(Real.exp 1*B)^ε := by
  obtain ⟨C,hC,hbound⟩ := reopenedCubeCoefficient_small_power ε hε
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro S D Ψ hΨ m f H₀ B ξ v hB hn hn'
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have ht : ∀ z, ‖rowTwist Ψ (m*excludedGenerator S) f 1 z‖ ≤ 1 :=
    rowTwist_norm Ψ hΨ (m*excludedGenerator S) f 1
  have hβ : ‖reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)‖ ≤
      C*(Real.exp 1*B)^ε := by
    apply (hbound H₀ _ ht _ (cubeIdeal_ne_zero F v)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn' hε.le) hC.le
  have hh := separatedCubeCoefficient_bound
    (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F u))
    (fun u => (Ideal.absNorm (cubeIdeal F u) : ℝ)) B ξ (C*(Real.exp 1*B)^ε)
    hB (by positivity) v hn hn' hβ
  convert hh using 1 ; ring
end OAI.CanonicalRowCompletion
