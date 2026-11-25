-- Prove2me | solution 1 for Newton.integral_norm_eq_toReal_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:56.867547+00:00
-- url     : https://prove2.me/submissions/c507d1bd-7025-41ba-abff-c8e08e323970

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Definitions.Def_Newton_Analysis_Convolution_Minkowski

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
open Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]
namespace Newton
theorem _root_.solution
    [NormedSpace ℝ E] {f : α → E} (hf : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by
  have hf_norm : Integrable (fun x => ‖f x‖) μ := hf.norm
  have h_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have h_eq :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_norm h_nonneg
  have h_int_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ :=
    integral_nonneg_of_ae h_nonneg
  have h_toReal := congrArg ENNReal.toReal h_eq
  simpa [ENNReal.toReal_ofReal, h_int_nonneg, ofReal_norm_eq_enorm] using h_toReal
end Newton
