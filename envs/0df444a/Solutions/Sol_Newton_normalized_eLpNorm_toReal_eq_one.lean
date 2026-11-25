-- Prove2me | solution 1 for Newton.normalized_eLpNorm_toReal_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:32:21.402051+00:00
-- url     : https://prove2.me/submissions/782672fc-4cf0-4633-81ab-68f95bc58483

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞) {f : α → ℝ} (hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0) :
    (eLpNorm (fun x => (1 / (eLpNorm f p μ).toReal) * f x) p μ).toReal = 1 := by
  set c : ℝ := (eLpNorm f p μ).toReal with hc
  have hc_ne_zero : c ≠ 0 := by simpa [hc] using hf_ne_zero
  have hc_nonneg : 0 ≤ c := ENNReal.toReal_nonneg
  have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (by simpa [hc, ne_comm] using hf_ne_zero)
  have h_scaling :
      eLpNorm (fun x => (1 / c) * f x) p μ =
        ‖(1 / c : ℝ)‖ₑ * eLpNorm f p μ := by
    change eLpNorm ((1 / c : ℝ) • f) p μ = _
    exact eLpNorm_const_smul (μ := μ) (p := p) (c := (1 / c : ℝ)) (f := f)
  have h_toReal :
      (eLpNorm (fun x => (1 / c) * f x) p μ).toReal = (1 / c) * c := by
    have h_nonneg : 0 ≤ (1 / c : ℝ) := one_div_nonneg.mpr hc_nonneg
    simpa [ENNReal.toReal_mul, hc, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      using congrArg ENNReal.toReal h_scaling
  have h_inv_mul : (1 / c : ℝ) * c = 1 := by
    simpa [one_div] using inv_mul_cancel₀ (a := c) hc_ne_zero
  exact h_toReal.trans h_inv_mul
end Newton
