-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.two_profile_seminorm_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:45:19.917582+00:00
-- url     : https://prove2.me/submissions/43ce8aef-a87a-405f-8b6c-daa7d99dc8e8

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_schwartzCLM_finite_seminorm_control


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
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution
    (T₁ T₂ : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₁ W) +
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₂ W) ≤
          C * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨t₁, C₁, hC₁, h₁⟩ := schwartzCLM_finite_seminorm_control T₁ s
  obtain ⟨t₂, C₂, hC₂, h₂⟩ := schwartzCLM_finite_seminorm_control T₂ s
  refine ⟨t₁ ∪ t₂, C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro W
  have ht₁ : t₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_left
  have ht₂ : t₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_right
  have hb₁ := (h₁ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₁ W) hC₁.le)
  have hb₂ := (h₂ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₂ W) hC₂.le)
  nlinarith
end OAI.EisensteinSchwartzPoisson
