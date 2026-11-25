-- Prove2me | solution 1 for Newton.minkowski_integral_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:36:42.559196+00:00
-- url     : https://prove2.me/submissions/2d9db49d-11d8-4cc1-b2d3-5c86c7f60a23

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Theorems.Thm_Newton_integral_norm_eq_toReal_lintegral
import Theorems.Thm_Newton_conjugate_exponent_formula
import Theorems.Thm_Newton_holder_kernel_pairing_bound
import Theorems.Thm_Newton_lp_duality_norm_le_of_pairing_bound
import Theorems.Thm_Newton_memLp_norm_integral


set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
open Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]
variable [SFinite μ] [SFinite ν]
namespace Newton
theorem _root_.solution
    [NormedSpace ℝ E] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ)
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by
  have h_meas : AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF)
  have h_integrable : Integrable (fun x => ∫ y, F x y ∂ν) μ := by
    have h_bound :
        ∀ᵐ x ∂μ, ‖∫ y, F x y ∂ν‖ ≤ ∫ y, ‖F x y‖ ∂ν :=
      ae_of_all _ fun x => norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    refine Integrable.mono'
      (hF_prod.integral_norm_prod_left)
      h_meas
      h_bound
  have h_norm_finite : (∫⁻ y, ‖(eLpNorm (fun x => F x y) p μ).toReal‖ₑ ∂ν) < ∞ :=
    hF_norm.hasFiniteIntegral
  -- The right-hand side is nonnegative, so we may work with real-valued estimates
  have h_rhs_nonneg :
      0 ≤ ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    integral_nonneg fun y => ENNReal.toReal_nonneg
  -- Reduce the claim to the integral formulation of the `L^p` seminorm
  have hp_ne_zero : p ≠ 0 := by
    intro h
    have : (1 : ℝ≥0∞) ≤ 0 := by simp [h] at hp
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1)) this
  have h_lhs_rewrite :=
    eLpNorm_eq_lintegral_rpow_enorm (μ := μ)
      (f := fun x => ∫ y, F x y ∂ν) hp_ne_zero hp_ne_top
  -- Work with the auxiliary scalar function given by the norm of the fibrewise integral.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  set B : ℝ := ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν
  have hB_nonneg : 0 ≤ B :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  by_cases hp_eq_one : p = 1
  · subst hp_eq_one
    have h_pointwise :
        ∀ᵐ x ∂μ, g x ≤ ∫ y, ‖F x y‖ ∂ν :=
      ae_of_all _ fun x =>
        norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    have hg_int : Integrable g μ := h_integrable.norm
    have h_integral_le :
        ∫ x, g x ∂μ ≤ ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ :=
      integral_mono_ae hg_int
        (hF_prod.integral_norm_prod_left)
        h_pointwise
    have h_inner_eq :
        ∀ᵐ y ∂ν,
          ∫ x, ‖F x y‖ ∂μ =
            (eLpNorm (fun x => F x y) 1 μ).toReal := by
      filter_upwards [hF_int] with y hy_int
      have h_eq :=
        integral_norm_eq_toReal_lintegral (μ := μ)
          (f := fun x => F x y) hy_int
      simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        using h_eq
    have h_double : ∫ x, ∫ y, ‖F x y‖ ∂ν ∂μ = B := by
      have h_swap :=by
        have h_norm_integrable :
            Integrable (Function.uncurry fun x y => ‖F x y‖) (μ.prod ν) :=
          hF_prod.norm
        simpa using
          MeasureTheory.integral_integral_swap
            (μ := μ) (ν := ν) (f := fun x y => ‖F x y‖)
            h_norm_integrable
      have h_congr := integral_congr_ae h_inner_eq
      simpa [g, B] using h_swap.trans h_congr
    have h_integral_bound : ∫ x, g x ∂μ ≤ B := by
      simpa [h_double] using h_integral_le
    have h_toReal_aux :=
      integral_norm_eq_toReal_lintegral (μ := μ)
        (f := fun x => ∫ y, F x y ∂ν) h_integrable
    have h_toReal :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ).toReal = ∫ x, g x ∂μ := by
      simpa [g, MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        using h_toReal_aux.symm
    have h_toReal_le :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) 1 μ).toReal ≤ B := by
      simpa [h_toReal] using h_integral_bound
    have h_memLp :
        MemLp (fun x => ∫ y, F x y ∂ν) 1 μ :=
      (memLp_one_iff_integrable : _ ↔ _).2 h_integrable
    have h_ne_top := h_memLp.eLpNorm_ne_top
    exact
      (le_ofReal_iff_toReal_le h_ne_top hB_nonneg).2 h_toReal_le
  · have hp_one_lt : 1 < p :=
      lt_of_le_of_ne' hp (by simpa [eq_comm] using hp_eq_one)
    have hp_lt_top : p < ∞ :=
      lt_of_le_of_ne le_top hp_ne_top
    obtain ⟨q, hpq, -⟩ :=
      conjugate_exponent_formula (p := p) hp_one_lt hp_lt_top
    have hq_gt_one : 1 < q := by
      rcases hpq with hpq | hpq
      · rcases hpq with ⟨hp_eq, _⟩
        simp [hp_eq] at hp_one_lt
      · rcases hpq with hpq | hpq
        · rcases hpq with ⟨hp_eq, _⟩
          simpa [hp_eq] using hp_lt_top.ne
        · rcases hpq with ⟨_, _, hq, _, _⟩
          exact hq
    have hg_mem : MemLp g p μ :=
      memLp_norm_integral (μ := μ) (ν := ν) (p := p)
        hp hp_ne_top hF hF_prod hF_memLp hF_norm
    have h_pairing_bound :
        ∀ φ : α → ℝ,
          MemLp φ q μ →
          (eLpNorm φ q μ).toReal ≤ 1 →
          Integrable (fun x => g x * φ x) μ →
          |∫ x, g x * φ x ∂μ| ≤ B := by
      intro φ hφ_mem hφ_norm _hφ_int
      have h_est :=
        holder_kernel_pairing_bound (μ := μ) (ν := ν)
          (p := p) (q := q) hpq
          hF hF_prod hF_memLp hF_norm hφ_mem
      have h_mul :
          (eLpNorm φ q μ).toReal * B ≤ B := by
        have := mul_le_mul_of_nonneg_right hφ_norm hB_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc]
          using this
      exact h_est.trans h_mul
    have h_norm_le :
        (eLpNorm g p μ).toReal ≤ B :=
      lp_duality_norm_le_of_pairing_bound (μ := μ)
        (p := p) (q := q)
        hp_one_lt hq_gt_one hpq hg_mem h_pairing_bound
    have h_ne_top :
        eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≠ ∞ := by
      have hg_ne_top := hg_mem.eLpNorm_ne_top
      simpa [g]
        using hg_ne_top
    have h_toReal_le :
        (eLpNorm (fun x => ∫ y, F x y ∂ν) p μ).toReal ≤ B := by
      simpa [g] using h_norm_le
    exact
      (le_ofReal_iff_toReal_le h_ne_top hB_nonneg).2 h_toReal_le
end Newton
