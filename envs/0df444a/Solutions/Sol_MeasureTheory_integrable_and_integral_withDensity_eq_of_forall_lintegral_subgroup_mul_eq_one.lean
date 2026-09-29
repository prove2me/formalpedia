-- Prove2me | solution 1 for MeasureTheory.integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a6d23a94-fb70-56f9-a06e-0a3475e18600

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Admissible

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
variable (H : Subgroup G)

private theorem measurable_coe_mul : Measurable (fun p : H × G => (p.1 : G) * p.2) :=
  (measurable_subtype_coe.comp measurable_fst).mul measurable_snd

variable {H}

section Lintegral

variable [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]

private theorem lintegral_mul_eq_of_invariant (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    {φ : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hφinv : ∀ (n : H) (g : G), φ ((n : G) * g) = φ g) :
    ∫⁻ g, φ g * ρ g ∂μ = ∫⁻ g, φ g * ρ' g ∂μ := by

  have hmeas : AEMeasurable (fun p : H × G => φ p.2 * ρ p.2 * ρ' ((p.1 : G) * p.2)) (μH.prod μ) :=
    (hφ.comp_snd.mul (hρ.comp measurable_snd).aemeasurable).mul (hρ'.comp (measurable_coe_mul H)).aemeasurable
  calc ∫⁻ g, φ g * ρ g ∂μ
      = ∫⁻ g, ∫⁻ n : H, φ g * ρ g * ρ' ((n : G) * g) ∂μH ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (φ g * ρ g) (f := fun n : H => ρ' ((n : G) * g))
          (hρ'.comp (measurable_subtype_coe.mul_const g)), hρ'1 g, mul_one]
    _ = ∫⁻ n : H, ∫⁻ g, φ g * ρ g * ρ' ((n : G) * g) ∂μ ∂μH :=
        lintegral_lintegral_swap hmeas.prod_swap
    _ = ∫⁻ n : H, ∫⁻ g, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μ ∂μH := by
        refine lintegral_congr fun n => ?_

        rw [← lintegral_mul_left_eq_self (fun g => φ g * ρ ((n : G)⁻¹ * g) * ρ' g) (n : G)]
        refine lintegral_congr fun g => ?_
        simp only [inv_mul_cancel_left, hφinv n g]
    _ = ∫⁻ g, ∫⁻ n : H, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μH ∂μ := by
        refine (lintegral_lintegral_swap ?_).symm
        exact ((hφ.comp_snd.mul
          (hρ.comp ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)).aemeasurable).mul
            (hρ'.comp measurable_snd).aemeasurable).prod_swap
    _ = ∫⁻ g, φ g * ρ' g ∂μ := by
        refine lintegral_congr fun g => ?_
        have h1 : ∫⁻ n : H, ρ ((n : G)⁻¹ * g) ∂μH = 1 := by
          rw [← hρ1 g, ← hinv (fun n : H => ρ ((n : G) * g))]
          simp only [Subgroup.coe_inv]
        calc ∫⁻ n : H, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μH
            = ∫⁻ n : H, (φ g * ρ' g) * ρ ((n : G)⁻¹ * g) ∂μH := by
              refine lintegral_congr fun n => ?_; ring
          _ = φ g * ρ' g := by
              rw [lintegral_const_mul (φ g * ρ' g) (f := fun n : H => ρ ((n : G)⁻¹ * g))
                (hρ.comp (measurable_subtype_coe.inv.mul_const g)), h1, mul_one]

end Lintegral

section Descent

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem measurePreserving_coe_mul :
    MeasurePreserving (fun p : H × G => (p.1, (p.1 : G) * p.2)) (μH.prod μ) (μH.prod μ) :=
  (MeasurePreserving.id μH).skew_product (g := fun n : H => fun g : G => (n : G) * g) (measurable_coe_mul H)
    (ae_of_all _ fun n => map_mul_left_eq_self μ (n : G))

private theorem measurePreserving_coe_inv_mul [MeasurableInv G] :
    MeasurePreserving (fun p : H × G => (p.1, (p.1 : G)⁻¹ * p.2)) (μH.prod μ) (μH.prod μ) :=
  (MeasurePreserving.id μH).skew_product (g := fun n : H => fun g : G => (n : G)⁻¹ * g)
    ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)
    (ae_of_all _ fun n => map_mul_left_eq_self μ (n : G)⁻¹)

private theorem ae_ae_mul_notMem {S : Set G} (hS : MeasurableSet S) (hS0 : μ S = 0) :
    ∀ᵐ g ∂μ, ∀ᵐ n : H ∂μH, (n : G) * g ∉ S := by
  have hT : (μH.prod μ) ((fun p : H × G => (p.1 : G) * p.2) ⁻¹' S) = 0 := by
    have h1 : (fun p : H × G => (p.1 : G) * p.2) ⁻¹' S =
        (fun p : H × G => (p.1, (p.1 : G) * p.2)) ⁻¹' (Set.univ ×ˢ S) := by
      ext p; simp
    rw [h1, (measurePreserving_coe_mul μ μH).measure_preimage (MeasurableSet.univ.prod hS).nullMeasurableSet,
      Measure.prod_prod, hS0, mul_zero]
  have hT' : (μ.prod μH) (Prod.swap ⁻¹' ((fun p : H × G => (p.1 : G) * p.2) ⁻¹' S)) = 0 := by
    rw [(Measure.measurePreserving_swap (μ := μ) (ν := μH)).measure_preimage
      (measurable_coe_mul H hS).nullMeasurableSet, hT]
  have h3 : ∀ᵐ q : G × H ∂μ.prod μH, (q.2 : G) * q.1 ∉ S := by
    rw [ae_iff]
    convert hT' using 2
    ext q; simp
  exact Measure.ae_ae_of_ae_prod h3

private theorem aestronglyMeasurable_of_invariant {ρ : G → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρt : ∀ g, ρ g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hf : AEStronglyMeasurable f (μ.withDensity ρ)) : AEStronglyMeasurable f μ := by
  set f₀ := hf.mk f with hf₀def
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  have hae : ∀ᵐ g ∂μ, ρ g ≠ 0 → f g = f₀ g := (ae_withDensity_iff hρ).mp hf.ae_eq_mk

  set S := toMeasurable μ {g | ¬ (ρ g ≠ 0 → f g = f₀ g)} with hSdef
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : μ S = 0 := by rw [hSdef, measure_toMeasurable]; exact hae
  have hgood : ∀ g, g ∉ S → ρ g ≠ 0 → f g = f₀ g := fun g hg => by
    by_contra h; exact hg (subset_toMeasurable _ _ h)

  refine ⟨fun g => ∫ n : H, (ρ ((n : G) * g)).toReal • f₀ ((n : G) * g) ∂μH, ?_, ?_⟩
  · have : StronglyMeasurable (fun q : G × H => (ρ ((q.2 : G) * q.1)).toReal • f₀ ((q.2 : G) * q.1)) := by
      have hm : Measurable (fun q : G × H => (q.2 : G) * q.1) :=
        (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
      exact ((hρ.comp hm).ennreal_toReal.stronglyMeasurable).smul (hf₀.comp_measurable hm)
    exact this.integral_prod_right'
  · filter_upwards [ae_ae_mul_notMem μ μH hSm hS0] with g hg
    have h1 : (fun n : H => (ρ ((n : G) * g)).toReal • f₀ ((n : G) * g)) =ᵐ[μH]
        fun n : H => (ρ ((n : G) * g)).toReal • f g := by
      filter_upwards [hg] with n hn
      by_cases h0 : ρ ((n : G) * g) = 0
      · simp [h0]
      · rw [← hgood _ hn h0, hfinv]
    rw [integral_congr_ae h1, integral_smul_const, integral_toReal (f := fun n : H => ρ ((n : G) * g))
      (hρ.comp (measurable_subtype_coe.mul_const g)).aemeasurable
      (ae_of_all _ fun n => lt_top_iff_ne_top.mpr (hρt _)), hρ1 g, ENNReal.toReal_one, one_smul]

end Descent

section Bochner

variable [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [MeasurableMul₂ G] [MeasurableInv G] [SFinite μH] in

private theorem lintegral_inv_mul_eq_one (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ : G → ℝ≥0∞} (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (g : G) :
    ∫⁻ n : H, ρ ((n : G)⁻¹ * g) ∂μH = 1 := by
  rw [← hρ1 g, ← hinv (fun n : H => ρ ((n : G) * g))]
  simp only [Subgroup.coe_inv]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [μ.IsMulLeftInvariant] [SFinite μ] [CompleteSpace E] in

private theorem integrable_toReal_smul_of_integrable_withDensity {ρ : G → ℝ≥0∞} (hρ : Measurable ρ)
    (hρt : ∀ g, ρ g ≠ ∞) {f : G → E} (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable (fun g => (ρ g).toReal • f g) μ :=
  (integrable_withDensity_iff_integrable_smul' hρ (ae_of_all _ fun g => lt_top_iff_ne_top.mpr (hρt g))).mp hfi

private theorem integral_withDensity_eq_of_invariant (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    (hρt : ∀ g, ρ g ≠ ∞) (hρ't : ∀ g, ρ' g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable f (μ.withDensity ρ') ∧
      ∫ g, f g ∂μ.withDensity ρ' = ∫ g, f g ∂μ.withDensity ρ := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_invariant μ μH hρ hρ1 hρt hfinv hfi.aestronglyMeasurable
  have hf' : ∀ (n : H) (g : G), f ((n : G)⁻¹ * g) = f g := fun n g => by
    simpa only [Subgroup.coe_inv] using hfinv n⁻¹ g
  have hρ'lt : ∀ g, ρ' g < ∞ := fun g => lt_top_iff_ne_top.mpr (hρ't g)
  have hρlt : ∀ g, ρ g < ∞ := fun g => lt_top_iff_ne_top.mpr (hρt g)

  set A : H × G → E := fun p => (ρ p.2).toReal • ((ρ' ((p.1 : G) * p.2)).toReal • f p.2) with hAdef
  set B : H × G → E := fun p => (ρ ((p.1 : G)⁻¹ * p.2)).toReal • ((ρ' p.2).toReal • f p.2) with hBdef
  have hΨ := measurePreserving_coe_inv_mul μ μH
  have hAB : A ∘ (fun p : H × G => (p.1, (p.1 : G)⁻¹ * p.2)) = B := by
    funext p
    simp only [hAdef, hBdef, Function.comp, mul_inv_cancel_left, hf']
  have hA_meas : AEStronglyMeasurable A (μH.prod μ) := by
    have h1 : Measurable fun p : H × G => (ρ p.2).toReal := (hρ.comp measurable_snd).ennreal_toReal
    have h2 : Measurable fun p : H × G => (ρ' ((p.1 : G) * p.2)).toReal :=
      (hρ'.comp (measurable_coe_mul H)).ennreal_toReal
    exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.smul hfm.comp_snd)

  have hρf : Integrable (fun g => (ρ g).toReal • f g) μ :=
    integrable_toReal_smul_of_integrable_withDensity μ hρ hρt hfi
  have hA_int : Integrable A (μH.prod μ) := by
    refine (integrable_prod_iff' hA_meas).mpr ⟨ae_of_all _ fun g => ?_, ?_⟩
    · have : Integrable (fun n : H => (ρ' ((n : G) * g)).toReal) μH :=
        integrable_toReal_of_lintegral_ne_top (hρ'.comp (measurable_subtype_coe.mul_const g)).aemeasurable
          (by rw [hρ'1 g]; exact ENNReal.one_ne_top)
      exact (this.smul_const (f g)).smul ((ρ g).toReal)
    · have hnorm : (fun g => ∫ n : H, ‖A (n, g)‖ ∂μH) = fun g => ‖(ρ g).toReal • f g‖ := by
        funext g
        have h1 : ∀ n : H, ‖A (n, g)‖ = (ρ g).toReal * ((ρ' ((n : G) * g)).toReal * ‖f g‖) := fun n => by
          simp only [hAdef, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        simp_rw [h1]
        rw [integral_const_mul, integral_mul_const, integral_toReal (f := fun n : H => ρ' ((n : G) * g))
          (hρ'.comp (measurable_subtype_coe.mul_const g)).aemeasurable (ae_of_all _ fun n => hρ'lt _),
          hρ'1 g, ENNReal.toReal_one, one_mul, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      rw [hnorm]
      exact hρf.norm
  have hB_int : Integrable B (μH.prod μ) := by
    rw [← hAB]; exact hΨ.integrable_comp_of_integrable hA_int

  have hA_iter : ∫ p, A p ∂μH.prod μ = ∫ g, (ρ g).toReal • f g ∂μ := by
    rw [integral_prod_symm A hA_int]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hAdef]
    rw [integral_smul, integral_smul_const, integral_toReal (f := fun n : H => ρ' ((n : G) * g))
      (hρ'.comp (measurable_subtype_coe.mul_const g)).aemeasurable (ae_of_all _ fun n => hρ'lt _),
      hρ'1 g, ENNReal.toReal_one, one_smul]
  have hB_inner : ∀ g, ∫ n : H, B (n, g) ∂μH = (ρ' g).toReal • f g := fun g => by
    simp only [hBdef]
    rw [integral_smul_const, integral_toReal (f := fun n : H => ρ ((n : G)⁻¹ * g))
      (hρ.comp (measurable_subtype_coe.inv.mul_const g)).aemeasurable (ae_of_all _ fun n => hρlt _),
      lintegral_inv_mul_eq_one μH hinv hρ1 g, ENNReal.toReal_one, one_smul]
  have hB_iter : ∫ p, B p ∂μH.prod μ = ∫ g, (ρ' g).toReal • f g ∂μ := by
    rw [integral_prod_symm B hB_int]
    exact integral_congr_ae (ae_of_all _ hB_inner)
  have hAB_int : ∫ p, A p ∂μH.prod μ = ∫ p, B p ∂μH.prod μ := by
    have h := integral_map (μ := μH.prod μ) hΨ.measurable.aemeasurable
      (f := A) (by rw [hΨ.map_eq]; exact hA_meas)
    rw [hΨ.map_eq] at h
    rw [h, ← hAB]; rfl
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hρ' (ae_of_all _ hρ'lt)]
    have := hB_int.integral_prod_right
    exact this.congr (ae_of_all _ hB_inner)
  · rw [integral_withDensity_eq_integral_toReal_smul hρ' (ae_of_all _ hρ'lt),
      integral_withDensity_eq_integral_toReal_smul hρ (ae_of_all _ hρlt), ← hB_iter, ← hAB_int, hA_iter]

end Bochner

end Admissible

end

theorem solution
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    (hρt : ∀ g, ρ g ≠ ∞) (hρ't : ∀ g, ρ' g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable f (μ.withDensity ρ') ∧
      ∫ g, f g ∂μ.withDensity ρ' = ∫ g, f g ∂μ.withDensity ρ :=
  Admissible.integral_withDensity_eq_of_invariant μ μH hinv hρ hρ' hρ1 hρ'1 hρt hρ't hfinv hfi

#print axioms solution

end S_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
end P2MW
export P2MW.S_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one (solution)
