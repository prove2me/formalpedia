-- Prove2me | solution 1 for Newton.holder_kernel_pairing_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:34:08.93054+00:00
-- url     : https://prove2.me/submissions/4c150175-2514-442e-aeeb-75ab781141b5

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Theorems.Thm_Newton_holder_inequality

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {β : Type*} [MeasurableSpace β]
variable {ν : Measure β}
namespace Newton
theorem _root_.solution
    [NormedSpace ℝ E] [SFinite μ] [SFinite ν]
    (p q : ℝ≥0∞) (hpq : IsConjugateExponent p q)
    {F : α → β → E} {φ : α → ℝ}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν)
    (hφ_mem : MemLp φ q μ) :
    |∫ x, ‖∫ y, F x y ∂ν‖ * φ x ∂μ|
      ≤ (eLpNorm φ q μ).toReal *
        ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
  -- Unpack the integrability information furnished by the product assumptions.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := ν)
        (f := Function.uncurry F) hF_meas).mp hF_prod
  have h_integrable_slices :
      ∀ᵐ x ∂μ, Integrable (fun y => F x y) ν := by
    simpa [Function.uncurry] using h_prod_info.1
  have h_integrable_norm :
      Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := by
    simpa [Function.uncurry] using h_prod_info.2
  -- Pointwise control of the pairing integrand by a simpler positive majorant.
  have h_pointwise_bound :
      (fun x => |‖∫ y, F x y ∂ν‖ * φ x|)
        ≤ᵐ[μ] fun x => (∫ y, ‖F x y‖ ∂ν) * |φ x| := by
    refine h_integrable_slices.mono ?_
    intro x _
    have hnorm_le :
        ‖∫ y, F x y ∂ν‖ ≤ ∫ y, ‖F x y‖ ∂ν := by
      simpa using (norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y))
    have h_abs_mul :
        |‖∫ y, F x y ∂ν‖ * φ x|
          = ‖∫ y, F x y ∂ν‖ * |φ x| := by
      have h_nonneg : 0 ≤ ‖∫ y, F x y ∂ν‖ := norm_nonneg _
      simp [abs_mul, abs_of_nonneg h_nonneg]
    have h_nonneg_abs : 0 ≤ |φ x| := abs_nonneg _
    have h_mul_le :
        ‖∫ y, F x y ∂ν‖ * |φ x|
          ≤ (∫ y, ‖F x y‖ ∂ν) * |φ x| :=
      mul_le_mul_of_nonneg_right hnorm_le h_nonneg_abs
    simpa [h_abs_mul]
  -- Apply Hölder to each fibre to control the inner integral with respect to `μ`.
  have h_holder_fibre :
      ∀ᵐ y ∂ν,
        Integrable (fun x => ‖F x y‖ * |φ x|) μ ∧
          ∫ x, ‖F x y‖ * |φ x| ∂μ
            ≤ (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal := by
    refine hF_memLp.mono ?_
    intro y hy
    have h_holder :=
      holder_inequality (μ := μ) (p := p) (q := q) hpq
        (f := fun x => F x y) (g := fun x => φ x)
        hy hφ_mem
    constructor
    · simpa using h_holder.1
    · simpa using h_holder.2
  have h_holder_integrable :
      ∀ᵐ y ∂ν, Integrable (fun x => ‖F x y‖ * |φ x|) μ :=
    h_holder_fibre.mono fun _ hy => hy.1
  have h_holder_bound' :
      (fun y => ∫ x, ‖F x y‖ * |φ x| ∂μ)
        ≤ᵐ[ν]
          fun y =>
            (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal :=
    h_holder_fibre.mono fun _ hy => hy.2
  have hφ_norm_nonneg : 0 ≤ (eLpNorm φ q μ).toReal := ENNReal.toReal_nonneg
  have h_bound_integrable :
      Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν := hF_norm
  have h_bound_integrable' :
      Integrable (fun y =>
        (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal) ν := by
    simpa [mul_comm] using
      (h_bound_integrable.mul_const ((eLpNorm φ q μ).toReal))
  have h_integral_norm_nonneg :
      0 ≤ ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
    have h_nonneg : 0 ≤ᵐ[ν] fun y => (eLpNorm (fun x => F x y) p μ).toReal :=
      Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
    exact integral_nonneg_of_ae h_nonneg
  have h_rhs_nonneg :
      0 ≤ (eLpNorm φ q μ).toReal *
          ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    mul_nonneg hφ_norm_nonneg h_integral_norm_nonneg
  -- Package the nonnegative kernel used for the Fubini step.
  set G : α → β → ℝ := fun x y => ‖F x y‖ * |φ x| with hG_def
  have hG_nonneg : ∀ x y, 0 ≤ G x y := by
    intro x y
    have h₁ : 0 ≤ ‖F x y‖ := norm_nonneg _
    have h₂ : 0 ≤ |φ x| := abs_nonneg _
    simpa [G, hG_def, mul_comm] using mul_nonneg h₁ h₂
  -- Express the iterated integral of the kernel via Fubini.
  have hG_integrable : Integrable (Function.uncurry G) (μ.prod ν) := by
    -- First, record that the kernel is almost everywhere strongly measurable.
    have hF_norm_aesm :
        AEStronglyMeasurable
          (fun z : α × β => ‖F z.1 z.2‖)
          (μ.prod ν) := hF_meas.norm
    have hφ_aesm : AEStronglyMeasurable φ μ := hφ_mem.aestronglyMeasurable
    have hφ_prod_aesm :
        AEStronglyMeasurable (fun z : α × β => |φ z.1|) (μ.prod ν) := by
      simpa [Real.norm_eq_abs] using (hφ_aesm.comp_fst).norm
    have hG_aesm :
        AEStronglyMeasurable (Function.uncurry G) (μ.prod ν) :=
      (hF_norm_aesm.mul hφ_prod_aesm).congr
        (Filter.Eventually.of_forall fun ⟨x, y⟩ => by simp [Function.uncurry, G, hG_def, Pi.mul_apply])
    -- Convert the slice-wise lintegral into a real integral using nonnegativity.
    have h_lintegral_eq :
        ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν
          = ∫⁻ y, ENNReal.ofReal (∫ x, G x y ∂μ) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [h_holder_integrable] with y hy
      have h_nonneg : 0 ≤ᵐ[μ] fun x => G x y :=
        Filter.Eventually.of_forall fun x => hG_nonneg x y
      have h_eq :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hy h_nonneg
      simpa [Function.uncurry, G, hG_def] using h_eq.symm
    -- Use the Hölder bound to control the iterated lintegral.
    have h_lintegral_bound :
        ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν
          ≤ ∫⁻ y,
              ENNReal.ofReal
                ((eLpNorm (fun x => F x y) p μ).toReal *
                  (eLpNorm φ q μ).toReal) ∂ν := by
      have h_ofReal_bound :
          (fun y => ENNReal.ofReal (∫ x, G x y ∂μ))
            ≤ᵐ[ν]
              fun y =>
                ENNReal.ofReal
                  ((eLpNorm (fun x => F x y) p μ).toReal *
                    (eLpNorm φ q μ).toReal) :=
        h_holder_bound'.mono fun y hy => by
          exact ENNReal.ofReal_le_ofReal hy
      have := lintegral_mono_ae h_ofReal_bound
      simpa [h_lintegral_eq]
        using this
    -- The dominating function on the right-hand side is integrable, hence finite.
    have h_bound_nonneg :
        0 ≤ᵐ[ν]
            fun y =>
              (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal :=
      Filter.Eventually.of_forall fun y =>
        by
          have h1 : 0 ≤ (eLpNorm (fun x => F x y) p μ).toReal :=
            ENNReal.toReal_nonneg
          have h2 : 0 ≤ (eLpNorm φ q μ).toReal :=
            ENNReal.toReal_nonneg
          exact mul_nonneg h1 h2
    have h_bound_lintegral_lt_top :
        ∫⁻ y,
            ENNReal.ofReal
              ((eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal) ∂ν <
            ∞ := by
      have h_eq :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_bound_integrable' h_bound_nonneg).symm
      rw [h_eq]
      simp [ENNReal.ofReal_lt_top]
    -- Combine the estimates to obtain finiteness of the product lintegral.
    have h_prod_lintegral_lt_top :
        ∫⁻ z, ENNReal.ofReal (Function.uncurry G z) ∂μ.prod ν < ∞ := by
      have h_ofReal_aemeas :
          AEMeasurable (fun z : α × β => ENNReal.ofReal (G z.1 z.2)) (μ.prod ν) :=
        (hG_aesm.aemeasurable).ennreal_ofReal
      have h_prod_eq :
          ∫⁻ z, ENNReal.ofReal (G z.1 z.2) ∂μ.prod ν
            = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν :=
        MeasureTheory.lintegral_prod_symm (μ := μ) (ν := ν)
          (f := fun z : α × β => ENNReal.ofReal (G z.1 z.2)) h_ofReal_aemeas
      have h_iter_lt_top :
          ∫⁻ y, ∫⁻ x, ENNReal.ofReal (G x y) ∂μ ∂ν < ∞ :=
        lt_of_le_of_lt h_lintegral_bound h_bound_lintegral_lt_top
      have h_prod_lt_top :
          ∫⁻ z, ENNReal.ofReal (G z.1 z.2) ∂μ.prod ν < ∞ := by
        exact h_prod_eq ▸ h_iter_lt_top
      simpa [Function.uncurry]
        using h_prod_lt_top
    -- Assemble the integrability statement.
    have h_norm_lintegral_eq :
        ∫⁻ z, ‖Function.uncurry G z‖ₑ ∂μ.prod ν
          = ∫⁻ z, ENNReal.ofReal (Function.uncurry G z) ∂μ.prod ν := by
      refine lintegral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro z
      have hz_nonneg : 0 ≤ Function.uncurry G z := hG_nonneg z.1 z.2
      have hz_abs : |Function.uncurry G z| = Function.uncurry G z :=
        abs_of_nonneg hz_nonneg
      calc
        ‖Function.uncurry G z‖ₑ
            = ENNReal.ofReal ‖Function.uncurry G z‖ := by
              simpa using (ofReal_norm_eq_enorm (Function.uncurry G z)).symm
        _ = ENNReal.ofReal (Function.uncurry G z) := by
              simp [Real.norm_eq_abs, hz_abs]
    have h_hasFiniteIntegral :
        HasFiniteIntegral (Function.uncurry G) (μ.prod ν) := by
      simpa [HasFiniteIntegral, h_norm_lintegral_eq]
        using h_prod_lintegral_lt_top
    exact ⟨hG_aesm, h_hasFiniteIntegral⟩
  have h_integral_swap :
      ∫ x, ∫ y, G x y ∂ν ∂μ = ∫ y, ∫ x, G x y ∂μ ∂ν := by
    have hG_meas :
        AEStronglyMeasurable (Function.uncurry G) (μ.prod ν) :=
      hG_integrable.aestronglyMeasurable
    simpa [Function.uncurry, G, hG_def]
      using
        MeasureTheory.integral_integral_swap
          (μ := μ) (ν := ν) (f := fun x y => G x y)
          hG_integrable
  -- Control the integral of the pairing using the positive kernel `G`.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖ * φ x
  set majorant : α → ℝ := fun x => ∫ y, G x y ∂ν
  have h_majorant_integrable : Integrable majorant μ :=
    hG_integrable.integral_prod_left
  have h_majorant_nonneg : 0 ≤ᵐ[μ] majorant :=
    Filter.Eventually.of_forall fun x => by
      have h_const_nonneg : 0 ≤ |φ x| := abs_nonneg _
      have h_integrand_nonneg : ∀ y, 0 ≤ G x y := fun y => by
        have h_norm_nonneg : 0 ≤ ‖F x y‖ := norm_nonneg _
        simpa [G, hG_def, mul_comm, mul_left_comm, mul_assoc]
          using mul_nonneg h_norm_nonneg h_const_nonneg
      have h_nonneg : 0 ≤ ∫ y, G x y ∂ν :=
        integral_nonneg fun y => h_integrand_nonneg y
      simpa [majorant]
        using h_nonneg
  have h_majorant_ae_eq :
      majorant =ᵐ[μ]
        fun x => (∫ y, ‖F x y‖ ∂ν) * |φ x| := by
    refine h_integrable_slices.mono ?_
    intro x hx
    have h_const_mul :
        ∫ y, G x y ∂ν
          = |φ x| * ∫ y, ‖F x y‖ ∂ν := by
      simpa [majorant, G, hG_def, mul_comm, mul_left_comm, mul_assoc]
        using integral_const_mul (μ := ν) (r := |φ x|)
          (f := fun y => ‖F x y‖)
    simpa [majorant, G, hG_def, mul_comm, mul_left_comm, mul_assoc]
      using h_const_mul
  have h_abs_le_majorant :
      ∀ᵐ x ∂μ, |g x| ≤ majorant x := by
    filter_upwards [h_pointwise_bound, h_majorant_ae_eq] with x hx_bound hx_eq
    have hx_bound' :
        |g x| ≤ (∫ y, ‖F x y‖ ∂ν) * |φ x| := by
      simpa [g, mul_comm, mul_left_comm, mul_assoc] using hx_bound
    have hx_majorant :
        (∫ y, ‖F x y‖ ∂ν) * |φ x| = majorant x := by
      simpa using hx_eq.symm
    simpa [hx_majorant] using hx_bound'
  -- Establish integrability of the pairing integrand via domination by `majorant`.
  have h_g_aesm : AEStronglyMeasurable g μ := by
    have h_intF : Integrable (fun x => ∫ y, F x y ∂ν) μ :=
      hF_prod.integral_prod_left
    have h_intF_norm :
        AEStronglyMeasurable (fun x => ‖∫ y, F x y ∂ν‖) μ :=
      (h_intF.aestronglyMeasurable.norm)
    have hφ_aesm' : AEStronglyMeasurable φ μ := hφ_mem.aestronglyMeasurable
    exact h_intF_norm.mul hφ_aesm'
  have h_g_integrable : Integrable g μ :=
    Integrable.mono' h_majorant_integrable h_g_aesm
      (h_abs_le_majorant.mono fun _ hx => by
        simpa [Real.norm_eq_abs] using hx)
  -- Pass to absolute values and compare with the iterated integral of `G`.
  have h_abs_integral_le_majorant :
      |∫ x, g x ∂μ| ≤ ∫ x, majorant x ∂μ := by
    calc
      |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ :=
        by
          simpa using
            (abs_integral_le_integral_abs (μ := μ) (f := g))
      _ ≤ ∫ x, majorant x ∂μ :=
        integral_mono_ae (μ := μ)
          (f := fun x => |g x|) (g := majorant)
          h_g_integrable.abs h_majorant_integrable
          (h_abs_le_majorant.mono fun _ hx => hx)
  -- Rewrite the majorant integral using Fubini and bound it by Hölder.
  have h_majorant_eq : ∫ x, majorant x ∂μ = ∫ y, ∫ x, G x y ∂μ ∂ν := by
    simpa [majorant]
      using h_integral_swap
  have h_inner_integrable :
      Integrable (fun y => ∫ x, G x y ∂μ) ν :=
    hG_integrable.integral_prod_right
  have h_holder_bound_integral :
      ∫ y, ∫ x, G x y ∂μ ∂ν
        ≤ ∫ y,
            (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal ∂ν :=
    integral_mono_ae (μ := ν)
      (f := fun y => ∫ x, G x y ∂μ)
      (g := fun y =>
        (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal)
      h_inner_integrable h_bound_integrable'
      h_holder_bound'
  have h_majorant_bound :
      ∫ x, majorant x ∂μ
        ≤ (eLpNorm φ q μ).toReal *
            ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
    have h_const_mul :
        ∫ y, (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal ∂ν
          = (eLpNorm φ q μ).toReal * ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using integral_const_mul (μ := ν)
          (r := (eLpNorm φ q μ).toReal)
          (f := fun y => (eLpNorm (fun x => F x y) p μ).toReal)
    calc
      ∫ x, majorant x ∂μ
          = ∫ y, ∫ x, G x y ∂μ ∂ν := h_majorant_eq
      _ ≤ ∫ y,
            (eLpNorm (fun x => F x y) p μ).toReal * (eLpNorm φ q μ).toReal ∂ν :=
        h_holder_bound_integral
      _ = (eLpNorm φ q μ).toReal *
            ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
        h_const_mul
  -- Combine the estimates.
  have h_abs_integral_final :
      |∫ x, g x ∂μ|
        ≤ (eLpNorm φ q μ).toReal *
            ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν :=
    h_abs_integral_le_majorant.trans h_majorant_bound
  -- Conclude by substituting back the definition of `g`.
  simpa [g] using h_abs_integral_final
end Newton
