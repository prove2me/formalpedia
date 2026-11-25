-- Prove2me | solution 1 for Newton.lp_duality_exists_norm_one_attainer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:49:11.172802+00:00
-- url     : https://prove2.me/submissions/e48fd6f0-5b7d-4c8a-b7b3-720c4f220ba0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_normalized_eLpNorm_toReal_eq_one
import Theorems.Thm_Newton_exists_dual_pair_for_unit
import Theorems.Thm_Newton_integral_scaling_of_normalization

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ) (hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0) :
    ∃ g : α → ℝ,
      MemLp g q μ ∧
      (eLpNorm g q μ).toReal = 1 ∧
      Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ) = (eLpNorm f p μ).toReal := by
  set c : ℝ := (eLpNorm f p μ).toReal
  have hc_ne_zero : c ≠ 0 := hf_ne_zero
  set f₀ : α → ℝ := fun x => (1 / c) * f x with hf₀_def
  have hf₀_mem : MemLp f₀ p μ := by
    simpa [f₀, hf₀_def, c, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hf.const_mul (1 / c)
  have hf₀_norm_eq_one : (eLpNorm f₀ p μ).toReal = 1 := by
    have := normalized_eLpNorm_toReal_eq_one (μ := μ) (p := p) (f := f) hf_ne_zero
    simpa [f₀, hf₀_def, c]
  obtain ⟨g, hg_mem, hg_norm_one, hg_int, hg_eq⟩ :=
    exists_dual_pair_for_unit (μ := μ) (p := p) (q := q) hp hq hpq
      (f := f₀) hf₀_mem hf₀_norm_eq_one
  have hf_int : Integrable (fun x => f x * g x) μ := by
    have hf_scaled : Integrable (fun x => c * (f₀ x * g x)) μ := hg_int.const_mul c
    have h_ae :
        (fun x => c * (f₀ x * g x)) =ᵐ[μ]
          fun x => f x * g x :=
      Filter.Eventually.of_forall fun x => by
        simp [f₀, c, hc_ne_zero, mul_comm, mul_left_comm]
    exact Integrable.congr hf_scaled h_ae
  have h_integral_scaling :
      (∫ x, f x * g x ∂μ) =
        c * (∫ x, f₀ x * g x ∂μ) := by
    have := integral_scaling_of_normalization (μ := μ) (f := f) (g := g)
      (c := c) hc_ne_zero hf_int
    simpa [f₀, hf₀_def, c]
  have h_integral_f₀ : (∫ x, f₀ x * g x ∂μ) = 1 := by
    simpa [hf₀_norm_eq_one, hg_norm_one] using hg_eq
  refine ⟨g, hg_mem, hg_norm_one, hf_int, ?_⟩
  have hc_toReal : (eLpNorm f p μ).toReal = c := rfl
  calc
    (∫ x, f x * g x ∂μ)
        = c * (∫ x, f₀ x * g x ∂μ) := h_integral_scaling
    _ = c := by simp [h_integral_f₀]
    _ = (eLpNorm f p μ).toReal := hc_toReal
end Newton
