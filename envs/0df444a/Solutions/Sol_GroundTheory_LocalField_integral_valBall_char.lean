-- Prove2me | solution 1 for GroundTheory.LocalField.integral_valBall_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:58:33.574566+00:00
-- url     : https://prove2.me/submissions/4c9b79b8-f69f-469a-a1fd-b0c88cb4e260

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_eq_mul_of_ne_one
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
open scoped Classical
namespace GroundTheory.LocalField
theorem _root_.solution (χ : AddChar K Circle) (k : ℤ) :
    ∫ x in valBall K k, (χ x : ℂ) ∂μ =
      if IsTrivialOn χ k then (μ.real (valBall K k) : ℂ) else 0 := by
  classical
  split_ifs with h
  · have e : ∀ x ∈ (valBall K k : Set K), (χ x : ℂ) = 1 := fun x hx => by simp [h x hx]
    rw [setIntegral_congr_fun (measurableSet_valBall k) e, setIntegral_const, Complex.real_smul,
      mul_one]
  · obtain ⟨h₀, hh₀, hne⟩ : ∃ h₀ ∈ valBall K k, χ h₀ ≠ 1 := by simpa [IsTrivialOn] using h
    let g : K → ℂ := (valBall K k : Set K).indicator fun x => (χ x : ℂ)
    have hg : ∀ x, g (h₀ + x) = (χ h₀ : ℂ) * g x := by
      intro x
      have hiff : h₀ + x ∈ valBall K k ↔ x ∈ valBall K k :=
        ⟨fun h' => by simpa using sub_mem h' hh₀, fun h' => add_mem hh₀ h'⟩
      by_cases hx : x ∈ valBall K k
      · simp [g, Set.indicator_of_mem (show x ∈ (valBall K k : Set K) from hx),
          Set.indicator_of_mem (show h₀ + x ∈ (valBall K k : Set K) from hiff.mpr hx),
          AddChar.map_add_eq_mul]
      · simp [g, Set.indicator_of_notMem (show x ∉ (valBall K k : Set K) from hx),
          Set.indicator_of_notMem (show h₀ + x ∉ (valBall K k : Set K) from mt hiff.mp hx)]
    have key : ∫ x in valBall K k, (χ x : ℂ) ∂μ = (χ h₀ : ℂ) * ∫ x in valBall K k, (χ x : ℂ) ∂μ :=
      calc ∫ x in valBall K k, (χ x : ℂ) ∂μ = ∫ x, g x ∂μ :=
            (integral_indicator (measurableSet_valBall k)).symm
        _ = ∫ x, g (h₀ + x) ∂μ := (integral_add_left_eq_self g h₀).symm
        _ = ∫ x, (χ h₀ : ℂ) * g x ∂μ := by simp only [hg]
        _ = (χ h₀ : ℂ) * ∫ x in valBall K k, (χ x : ℂ) ∂μ := by
            rw [integral_const_mul, integral_indicator (measurableSet_valBall k)]
    exact eq_zero_of_eq_mul_of_ne_one (fun h' => hne (Circle.coe_eq_one.mp h')) key
end GroundTheory.LocalField
