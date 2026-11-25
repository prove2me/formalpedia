-- Prove2me | solution 1 for Newton.tonelli_norm_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:06:53.20824+00:00
-- url     : https://prove2.me/submissions/f92d4dcb-6432-42a0-b586-d68b3f3da0d5

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
variable [AddCommGroup G]
namespace Newton
theorem _root_.solution
    {f g : G → ℂ}
    [MeasurableAdd₂ G]
    [MeasurableNeg G]
    [μ.IsAddRightInvariant]
    [SFinite μ]
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hf_int : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ < ∞)
    (hg_int : ∫⁻ y, ENNReal.ofReal ‖g y‖ ∂μ < ∞) :
    ∫⁻ p, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ) < ∞ := by
  -- Package the absolute values as ℝ≥0∞-valued functions.
  set Af : G → ℝ≥0∞ := fun x => ENNReal.ofReal ‖f x‖
  set Ag : G → ℝ≥0∞ := fun y => ENNReal.ofReal ‖g y‖
  have hAf_aemeas : AEMeasurable Af μ := by
    simpa [Af] using (hf_meas.norm.aemeasurable.ennreal_ofReal)
  have hAg_aemeas : AEMeasurable Ag μ := by
    simpa [Ag] using (hg_meas.norm.aemeasurable.ennreal_ofReal)
  have hAf_lt_top : (∫⁻ x, Af x ∂μ) < ∞ := by simpa [Af] using hf_int
  have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by simpa [Ag] using hg_int
  -- Pointwise rewrite of the kernel in terms of Af and Ag.
  have h_kernel_eq :
      (fun p : G × G =>
        ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖))
        = fun p : G × G => Af (p.1 - p.2) * Ag p.2 := by
    funext p
    simp [Af, Ag, ENNReal.ofReal_mul, mul_comm]
  -- Measurability data for the composed kernels.
  have hAg_prod_aemeas :
      AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
    hAg_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have h_prod_aemeas :
      AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
    (hAf_aemeas.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul
        hAg_prod_aemeas
  -- Change of variables via the measure-preserving shear.
  set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
  have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
    measurePreserving_sub_prod (μ := μ) (ν := μ)
  have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
  have h_change :
      ∫⁻ q : G × G, Af (q.1 - q.2) * Ag q.2 ∂(μ.prod μ)
        = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
    have h_meas_map :
        AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
          (Measure.map τ (μ.prod μ)) := by
      simpa [h_map] using h_prod_aemeas
    have h_comp :=
      lintegral_map' h_meas_map
        (aemeasurable_id'.comp_measurable h_pres.measurable)
    have h_eval :
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
      simpa [τ, h_map] using h_comp
    simpa [τ] using h_eval.symm
  -- Evaluate the remaining product integral via Tonelli.
  have h_tonelli :
      ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    have h_split :=
      MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
        (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
    have h_inner :
        ∀ x, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
      intro x
      simpa using
        lintegral_const_mul'' (μ := μ) (r := Af x) (f := Ag) hAg_aemeas
    have h_outer :
        ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ
          = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
      simpa [mul_comm] using
        lintegral_mul_const'' (μ := μ)
          (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_aemeas
    calc
      ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = ∫⁻ x, ∫⁻ y, Af x * Ag y ∂μ ∂μ := by
              simpa [Function.uncurry] using h_split
      _ = ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ := by
              simp [h_inner]
      _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by simp [mul_comm]
  -- Assemble the pieces.
  have h_kernel_eval :
      ∫⁻ p : G × G,
          ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    have h_eq : ∀ p : G × G,
        ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) = Af (p.1 - p.2) * Ag p.2 := by
      intro p
      simp only [Af, Ag, ENNReal.ofReal_mul (norm_nonneg _)]
    calc
      ∫⁻ p, ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) ∂(μ.prod μ)
          = ∫⁻ p, Af (p.1 - p.2) * Ag p.2 ∂(μ.prod μ) := by simp only [h_eq]
      _ = ∫⁻ p, Af p.1 * Ag p.2 ∂(μ.prod μ) := h_change
      _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := h_tonelli
  have h_kernel_eval' :
      ∫⁻ p : G × G, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ)
        = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by
    simpa [Af, Ag, norm_mul, ENNReal.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      using h_kernel_eval
  have h_fin : (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) < ∞ :=
    ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
  have h_prod_fin :
      ∫⁻ p : G × G,
          ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) ∂(μ.prod μ) < ∞ := by
    rw [h_kernel_eval]
    exact h_fin
  have h_kernel_fin :
      ∫⁻ p : G × G, ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖ ∂(μ.prod μ) < ∞ := by
    have h_eq : ∀ p : G × G,
        ENNReal.ofReal ‖f (p.1 - p.2) * g p.2‖
          = ENNReal.ofReal (‖f (p.1 - p.2)‖ * ‖g p.2‖) := by
      intro p
      rw [norm_mul]
    simp_rw [h_eq]
    exact h_prod_fin
  exact h_kernel_fin
end Newton
