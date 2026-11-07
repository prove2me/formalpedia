-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.norm_secondPoisson_zeroMode_fixed_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:16:56.130188+00:00
-- url     : https://prove2.me/submissions/e24ca11e-1300-4ceb-a0db-faf863a77002

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_ConcretePrimeRowBridge_norm_conjugateIdealRowSum_zeroMode_le
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply



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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (ξ ρ : Ideal O → ℂ) (A : ℕ → ℂ)
    (hξ : ∀ I ∈ F, ‖ξ I‖ ≤ 1) (hρ : ∀ I ∈ F, ‖ρ I‖ ≤ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    let C : Ideal O → ℂ := fun I => ξ I * ρ I * A (Ideal.absNorm I)
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  dsimp only
  refine (norm_conjugateIdealRowSum_zeroMode_le F hFpos hFgood
    (fun I => ξ I * ρ I * A (Ideal.absNorm I)) W scale).trans ?_
  gcongr with I hI
  simp only [norm_mul]
  calc
    ‖ξ I‖ * ‖ρ I‖ * ‖A (Ideal.absNorm I)‖ ≤
        1 * 1 * ‖A (Ideal.absNorm I)‖ := by gcongr; exact hξ I hI; exact hρ I hI
    _ = _ := by ring
end OAI.ConcretePrimeRowBridge
