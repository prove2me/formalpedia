-- Prove2me | solution 1 for Newton.integral_scaling_of_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:32:23.723846+00:00
-- url     : https://prove2.me/submissions/f2be4e1a-3973-408b-aef6-b9bd54165698

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
    {f g : α → ℝ} {c : ℝ} (hc_ne_zero : c ≠ 0)
    (h_int : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) =
      c * (∫ x, ((1 / c) * f x) * g x ∂μ) := by
  have h_integral_scaled :
      (∫ x, ((1 / c) * f x) * g x ∂μ) =
        (1 / c) * (∫ x, f x * g x ∂μ) := by
    have h := h_int.integral_smul (μ := μ) (c := (1 / c))
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using h
  set I : ℝ := ∫ x, f x * g x ∂μ with hI
  have h_cancel : c * c⁻¹ = 1 := by
    simpa [one_div] using mul_inv_cancel₀ hc_ne_zero
  have h_aux : ∫ x, ((1 / c) * f x) * g x ∂μ = c⁻¹ * I := by
    simpa [one_div] using h_integral_scaled
  have h_rhs : c * (∫ x, ((1 / c) * f x) * g x ∂μ) = I := by
    calc
      c * (∫ x, ((1 / c) * f x) * g x ∂μ)
          = c * (c⁻¹ * I) := by rw [h_aux]
      _ = (c * c⁻¹) * I := by simp [mul_assoc]
      _ = I := by simp [h_cancel, I]
  have h_rhs' : I = c * (∫ x, ((1 / c) * f x) * g x ∂μ) := h_rhs.symm
  calc
    ∫ x, f x * g x ∂μ = I := by simp [I]
    _ = c * (∫ x, ((1 / c) * f x) * g x ∂μ) := h_rhs'
end Newton
