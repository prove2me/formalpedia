-- Prove2me | solution 1 for Newton.holder_inequality_one_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:31.249907+00:00
-- url     : https://prove2.me/submissions/57fe5fcd-a897-4325-8db7-ea77d58f331f

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Newton
theorem _root_.solution
    (f : α → E) (g : α → F)
    (hf : Integrable f μ)
    (hg_ae : AEStronglyMeasurable g μ)
    (hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (∫ x, ‖f x‖ ∂μ) * (sInf {C | ∀ᵐ x ∂μ, ‖g x‖ ≤ C}) := by
  by_cases hμ : μ = 0
  · simp [hμ]
  set S := {C : ℝ | ∀ᵐ x ∂μ, ‖g x‖ ≤ C} with hS
  have hS_nonempty : S.Nonempty :=
    let ⟨C, hC⟩ := hg_bound
    ⟨max C 0, hC.mono fun x hx => hx.trans <| le_max_left _ _⟩
  have hf_norm : Integrable (fun x => ‖f x‖) μ := hf.norm
  set A := ∫ x, ‖f x‖ * ‖g x‖ ∂μ with hA
  set a := ∫ x, ‖f x‖ ∂μ with ha
  have ha_nonneg : 0 ≤ a := by
    have : ∀ x, 0 ≤ ‖f x‖ := fun x => norm_nonneg _
    simpa [ha] using integral_nonneg this
  have holder_with_bound : ∀ {C : ℝ}, C ∈ S → A ≤ a * C := by
    intro C hC
    have hC_ae : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := hC
    have hC_nonneg : 0 ≤ C :=
      by
        have hμ_univ_ne : μ (Set.univ : Set α) ≠ 0 :=
          by simpa [Measure.measure_univ_eq_zero] using hμ
        by_contra hCneg
        have hCneg' : C < 0 := lt_of_not_ge hCneg
        have hμset : μ {x | C < ‖g x‖} = 0 := by
          simpa [not_le] using (ae_iff).1 hC_ae
        have hset : {x | C < ‖g x‖} = (Set.univ : Set α) := by
          ext x
          have hx : C < ‖g x‖ := lt_of_lt_of_le hCneg' (norm_nonneg _)
          simp [hx]
        exact hμ_univ_ne <| by simpa [hset] using hμset
    have h_mul_le : (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => C * ‖f x‖ :=
      hC_ae.mono fun x hx =>
        by
          have hfx : 0 ≤ ‖f x‖ := norm_nonneg _
          have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
            (mul_le_mul_of_nonneg_left hx hfx : _)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have h_mul_abs : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C * ‖f x‖ :=
      hC_ae.mono fun x hx =>
        by
          have hfx : 0 ≤ ‖f x‖ := norm_nonneg _
          have hgx : 0 ≤ ‖g x‖ := norm_nonneg _
          have h_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hfx hgx
          have h_rhs_nonneg : 0 ≤ C * ‖f x‖ := mul_nonneg hC_nonneg hfx
          have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
            (mul_le_mul_of_nonneg_left hx hfx : _)
          simpa [Real.norm_of_nonneg h_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
            mul_comm, mul_left_comm, mul_assoc] using this
    have h_mul_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
      (hf_norm.aestronglyMeasurable.mul hg_ae.norm)
    have h_const_int : Integrable (fun x => C * ‖f x‖) μ := hf_norm.const_mul C
    have h_mul_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
      Integrable.mono' h_const_int h_mul_meas h_mul_abs
    have h_integral_le := integral_mono_ae h_mul_int h_const_int h_mul_le
    have h_integral_const : ∫ x, C * ‖f x‖ ∂μ = C * a := by
      simpa [ha, mul_comm] using
        integral_const_mul (μ := μ) (r := C) (f := fun x => ‖f x‖)
    have : A ≤ C * a := by
      simpa [A, h_integral_const] using h_integral_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h_eps : ∀ {ε : ℝ}, 0 < ε → A ≤ a * (sInf S + ε) := by
    intro ε hε
    obtain ⟨C, hC_mem, hC_lt⟩ := Real.lt_sInf_add_pos hS_nonempty hε
    have hAC : A ≤ a * C := holder_with_bound hC_mem
    have h_le : C ≤ sInf S + ε := le_of_lt hC_lt
    have h_order : a * C ≤ a * (sInf S + ε) :=
      mul_le_mul_of_nonneg_left h_le ha_nonneg
    exact hAC.trans h_order
  have hA_nonneg : 0 ≤ A :=
    by
      have : ∀ x, 0 ≤ ‖f x‖ * ‖g x‖ :=
        fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa [A] using integral_nonneg this
  have h_final : A ≤ a * sInf S := by
    by_cases ha_zero : a = 0
    · obtain ⟨C₀, hC₀⟩ := hS_nonempty
      have hA_le_zero : A ≤ 0 := by
        simpa [ha_zero] using holder_with_bound hC₀
      have hA_eq_zero : A = 0 :=
        le_antisymm hA_le_zero hA_nonneg
      simp [hA_eq_zero, ha_zero]
    · have ha_ne : a ≠ 0 := ha_zero
      have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using ha_ne)
      have h_eps' : ∀ {ε : ℝ}, 0 < ε → A ≤ a * sInf S + ε := by
        intro ε hε
        have hδpos : 0 < ε / a := div_pos hε ha_pos
        have hmain := h_eps hδpos
        have hmul : a * (sInf S + ε / a) = a * sInf S + ε := by
          simp [mul_add, div_eq_mul_inv, mul_left_comm, ha_ne]
        simpa [hmul, mul_comm, mul_left_comm, mul_assoc] using hmain
      have h_lt : ∀ {ε : ℝ}, 0 < ε → A < a * sInf S + ε := by
        intro ε hε
        have hhalf : 0 < ε / 2 := half_pos hε
        have hineq := h_eps' hhalf
        have hlt : a * sInf S + ε / 2 < a * sInf S + ε :=
          add_lt_add_right (half_lt_self hε) (a * sInf S)
        exact lt_of_le_of_lt hineq hlt
      exact (le_iff_forall_pos_lt_add).2 fun ε hε => h_lt hε
  simpa [A, a, S, mul_comm, mul_left_comm, mul_assoc] using h_final
end Newton
