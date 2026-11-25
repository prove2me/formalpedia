-- Prove2me | solution 1 for Newton.convolution_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:25.170376+00:00
-- url     : https://prove2.me/submissions/3f0d32df-1543-4076-a0af-62efdd3f4200

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Theorems.Thm_Newton_convolution_kernel_aestronglyMeasurable

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
open Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]
variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]
namespace Newton
theorem _root_.solution
    (f g : G → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by
  -- Basic measurability for the kernel
  have h_meas : AEStronglyMeasurable
      (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) :=
    convolution_kernel_aestronglyMeasurable (μ := μ)
      f g hf.aestronglyMeasurable hg.aestronglyMeasurable
  -- Work with the nonnegative integrand built from the norms of `f` and `g`.
  set Af : G → ℝ≥0∞ := fun x => ‖f x‖ₑ
  set Ag : G → ℝ≥0∞ := fun y => ‖g y‖ₑ
  have hAf_aemeas : AEMeasurable Af μ :=
    hf.aestronglyMeasurable.enorm
  have hAg_aemeas : AEMeasurable Ag μ :=
    hg.aestronglyMeasurable.enorm
  have hAf_lt_top : (∫⁻ x, Af x ∂μ) < ∞ := by
    simpa [Af, HasFiniteIntegral]
      using hf.hasFiniteIntegral
  have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by
    simpa [Ag, HasFiniteIntegral]
      using hg.hasFiniteIntegral
  -- Express the norm of the kernel pointwise in terms of `Af` and `Ag`.
  have h_norm_rewrite :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ))
        = ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ) := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro q
    simp [Af, Ag, mul_comm]
  -- Change variables via the measure-preserving map `(x, y) ↦ (x - y, y)`.
  set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
  have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
    measurePreserving_sub_prod (μ := μ) (ν := μ)
  have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
  have hAf_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1) (μ.prod μ) :=
    hAf_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
  have hAg_prod_aemeas :
      AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
    hAg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
    hAf_prod_aemeas.mul hAg_prod_aemeas
  have h_change :
      ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
    have h_integrand_map :
        AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
          (Measure.map τ (μ.prod μ)) := by
      simpa [h_map]
        using h_prod_aemeas
    have h_comp :=
      lintegral_map' h_integrand_map
        (aemeasurable_id'.comp_measurable h_pres.measurable)
    have h_comp' :
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
      simpa [τ, h_map]
        using h_comp
    simpa [τ]
      using h_comp'.symm
  -- Evaluate the remaining product integral via Tonelli.
  have h_tonelli :=
    MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
      (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
  have h_const_mul :
      ∀ x : G, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
    intro x
    simpa using
      (lintegral_const_mul'' (μ := μ)
        (r := Af x) (f := Ag) hAg_aemeas)
  have h_split :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ x : G, ∫⁻ y : G, Af x * Ag y ∂μ ∂μ := by
    simpa [Function.uncurry]
      using h_tonelli
  have h_point :
      (fun x : G => ∫⁻ y, Af x * Ag y ∂μ)
        = fun x : G => Af x * ∫⁻ y, Ag y ∂μ := by
    funext x
    exact h_const_mul x
  have h_outer :
      ∫⁻ x : G, Af x * ∫⁻ y : G, Ag y ∂μ ∂μ
        = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
    simpa [mul_comm]
      using
        (lintegral_mul_const'' (μ := μ)
          (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_aemeas)
  have h_lintegral_prod :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ x : G, ∫⁻ y : G, Af x * Ag y ∂μ ∂μ := h_split
      _ = ∫⁻ x : G, Af x * ∫⁻ y : G, Ag y ∂μ ∂μ := by
            simp [h_point]
      _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
            simp [mul_comm]
  -- Collect the previous computations to bound the kernel integral.
  have h_kernel_lintegral :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ))
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    calc
      ∫⁻ q, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ)
          = ∫⁻ q, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ) := h_norm_rewrite
      _ = ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ) := h_change
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := h_lintegral_prod
  have h_aux :
      (∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)) < ∞ := by
    simpa [h_change, h_lintegral_prod]
      using ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
  have h_kernel_fin :
      (∫⁻ q : G × G, ‖f (q.1 - q.2) * g q.2‖ₑ ∂(μ.prod μ)) < ∞ := by
    simpa [h_norm_rewrite]
      using h_aux
  exact ⟨h_meas, h_kernel_fin⟩
end Newton
