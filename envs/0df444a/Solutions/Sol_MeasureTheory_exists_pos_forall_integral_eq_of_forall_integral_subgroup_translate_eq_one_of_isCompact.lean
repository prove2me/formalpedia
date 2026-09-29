-- Prove2me | solution 1 for MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/aecf2adb-3f9c-5059-97a9-15f158e254c7

import Mathlib
import Theorems.Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact

set_option autoImplicit false

open MeasureTheory

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (C : Set G) (hC : IsCompact C) (hcov : ∀ g : G, ∃ t : T, ∃ k ∈ C, g = (t : G) * k) :
    ∃ κ : ℝ, 0 < κ ∧
      (∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
        ∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∀ w : G → ℝ, (∀ x, 0 ≤ w x) → Measurable w → HasCompactSupport w →
        (∀ x : G, ∫ t : T, w ((t : G) * x) ∂τ = 1) → ∫ x, w x ∂μ = κ := by
  obtain ⟨β, hβc, hβs, hβ0, hβ1⟩ :=
    MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
      T hT τ C hC hcov

  have indep : ∀ w₁ w₂ : G → ℝ, (∀ x, 0 ≤ w₁ x) → Measurable w₁ → HasCompactSupport w₁ →
      (∀ x : G, ∫ t : T, w₁ ((t : G) * x) ∂τ = 1) → (∀ x, 0 ≤ w₂ x) → Measurable w₂ → HasCompactSupport w₂ →
      (∀ x : G, ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) → ∫ x, w₁ x ∂μ = ∫ x, w₂ x ∂μ := by
    intro w₁ w₂ h1 m1 c1 s1 h2 m2 c2 s2
    have h := MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one T hT μ τ
      (fun _ => (1 : ℂ)) measurable_const ⟨1, fun _ => by simp⟩ (fun _ _ => rfl) w₁ w₂
      ⟨h1, m1, c1, fun x _ => s1 x⟩ ⟨h2, m2, c2, fun x _ => s2 x⟩
    simp only [one_mul] at h
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  refine ⟨∫ x, β x ∂μ, ?_, ⟨β, hβ0, hβc, hβs, hβ1⟩, fun w hw0 hwm hwc hws => indep w β hw0 hwm hwc hws hβ0 hβc.measurable hβs hβ1⟩

  have hne : ∃ x, β x ≠ 0 := by
    by_contra h
    push Not at h
    have := hβ1 1
    simp [h] at this
  obtain ⟨x, hx⟩ := hne
  exact hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hβs hβ0 hx

end S_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
end P2MW
export P2MW.S_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact (solution)
