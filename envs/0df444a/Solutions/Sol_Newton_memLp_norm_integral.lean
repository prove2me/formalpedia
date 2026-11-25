-- Prove2me | solution 1 for Newton.memLp_norm_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:31:48.779086+00:00
-- url     : https://prove2.me/submissions/ccd5b716-ebe9-447b-9097-38b19cf8a11e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_eLpNorm_norm_integral_lt_top

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    {F : α → β → E}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    MemLp (fun x => ‖∫ y, F x y ∂ν‖) p μ := by
  -- Basic measurability facts for the fibrewise integral and its norm.
  have h_integral_meas :
      AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF_meas)
  have h_norm_meas :
      AEStronglyMeasurable (fun x => ‖∫ y, F x y ∂ν‖) μ :=
    h_integral_meas.norm
  -- Extract the information on fibrewise integrability provided by `hF_prod`.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := ν)
      (f := Function.uncurry F) hF_meas).mp hF_prod
  have hF_int_left :
      ∀ᵐ x ∂μ, Integrable (fun y => F x y) ν := by
    simpa [Function.uncurry] using h_prod_info.1
  have h_majorant_int :
      Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := by
    simpa [Function.uncurry] using h_prod_info.2
  -- Pointwise domination of the norm by the integral of fibrewise norms.
  have h_pointwise :
      (fun x => ‖∫ y, F x y ∂ν‖)
        ≤ᵐ[μ]
          fun x => ∫ y, ‖F x y‖ ∂ν := by
    refine hF_int_left.mono ?_
    intro x hx
    have hx_bound :=
      norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    simpa using hx_bound
  -- The pointwise domination yields integrability of the normed integral.
  have h_norm_integrable :
      Integrable (fun x => ‖∫ y, F x y ∂ν‖) μ := by
    refine Integrable.mono' h_majorant_int h_norm_meas ?_
    exact h_pointwise.mono fun _ ha => by simpa using ha
  -- Work with the scalar helper `g`.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  have hg_meas : AEStronglyMeasurable g μ := h_norm_meas
  have hg_int : Integrable g μ := by
    simpa [g] using h_norm_integrable
  by_cases hp_eq_one : p = (1 : ℝ≥0∞)
  · subst hp_eq_one
    -- For `p = 1`, membership in `L¹` is equivalent to integrability.
    have hg_mem : MemLp g (1 : ℝ≥0∞) μ :=
      (memLp_one_iff_integrable : MemLp g (1 : ℝ≥0∞) μ ↔ Integrable g μ).2 hg_int
    simpa [g] using hg_mem
  -- For `p > 1`, the previous finiteness lemma applies directly.
  · have hp_ne_one : p ≠ (1 : ℝ≥0∞) := hp_eq_one
    have hp_one_lt : 1 < p :=
      lt_of_le_of_ne' hp (by simpa [eq_comm] using hp_ne_one)
    have hp_pos : (0 : ℝ≥0∞) < p :=
      lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ 1) hp_one_lt
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have h_lt_top :=
      eLpNorm_norm_integral_lt_top (μ := μ) (ν := ν) (p := p)
        hp_one_lt hp_ne_top hF_meas hF_prod hF_memLp hF_norm
    have hg_mem : MemLp g p μ := ⟨hg_meas, by simpa [g] using h_lt_top⟩
    simpa [g] using hg_mem
end Newton
