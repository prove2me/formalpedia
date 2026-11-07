-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.schwartzCLM_family_finite_seminorm_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:32:39.684409+00:00
-- url     : https://prove2.me/submissions/bccc5f50-5197-4699-9b79-b198e2ea10d4

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply


attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply

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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory
open scoped SchwartzMap ContDiff
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution
    (T : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K →
        SchwartzMap.seminorm ℝ 0 0 (T j W) +
          SchwartzMap.seminorm ℝ (2 * A) 0 (T j W) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let qj : ℕ → Seminorm ℝ 𝓢(ℝ, ℂ) := fun j =>
    (SchwartzMap.seminorm ℝ 0 0 + SchwartzMap.seminorm ℝ (2 * A) 0).comp
      (T j).toLinearMap
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) := ∑ j ∈ Finset.range (K + 1), qj j
  have hqfun : (q : 𝓢(ℝ, ℂ) → ℝ) = fun W => ∑ j ∈ Finset.range (K + 1),
      (SchwartzMap.seminorm ℝ 0 0 (T j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T j W)) := by
    funext W
    simp [q, qj]
  have hq : Continuous q := by
    rw [hqfun]
    apply continuous_finsetSum
    intro j hj
    exact (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp
        (T j).continuous).add
      (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2 * A, 0)).comp
        (T j).continuous)
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W j hj
    apply le_trans ?_ (Seminorm.le_def.mp hbound W)
    rw [hqfun]
    exact Finset.single_le_sum (f := fun i =>
      SchwartzMap.seminorm ℝ 0 0 (T i W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T i W))
      (by intro i hi; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
end OAI.EisensteinSchwartzPoisson
