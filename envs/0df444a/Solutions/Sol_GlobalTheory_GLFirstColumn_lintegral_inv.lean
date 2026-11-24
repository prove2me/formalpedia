-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:23.304811+00:00
-- url     : https://prove2.me/submissions/0cbb77d2-1dcb-4b7e-b39c-8e5e7da89992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_right
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_left
import Theorems.Thm_GlobalTheory_GLFirstColumn_of_mulM
import Theorems.Thm_GlobalTheory_GLFirstColumn_of_invM
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_mulM
import Theorems.Thm_GlobalTheory_GLFirstColumn_continuous_detM
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_invM
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_wt
import Theorems.Thm_GlobalTheory_GLFirstColumn_wt_mul
import Theorems.Thm_GlobalTheory_GLFirstColumn_wt_cancel
import Theorems.Thm_GlobalTheory_GLFirstColumn_wt_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {m : ℕ} (f : (Fin m → Fin m → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f (invM s) * wt s = ∫⁻ s, f s * wt s := by
  set μ : Measure (Fin m → Fin m → ℂ) := volume.withDensity wt with hμ
  have hint : ∀ g : (Fin m → Fin m → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂μ = ∫⁻ y, g y * wt y := by
    intro g hg
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ measurable_wt hg]
    simp only [Pi.mul_apply, mul_comm]
  haveI : SigmaFinite μ := SigmaFinite.withDensity_of_ne_top
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have hae : ∀ᵐ x ∂μ, (Matrix.of x).det ≠ 0 := by
    rw [hμ, ae_withDensity_iff measurable_wt]
    exact Filter.Eventually.of_forall fun x hx h => hx (wt_eq_zero x h)
  have hne : μ ≠ 0 := by
    intro h
    rw [hμ, withDensity_eq_zero_iff measurable_wt.aemeasurable] at h
    haveI : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Fin m → Fin m → ℂ)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    have ho : IsOpen {x : Fin m → Fin m → ℂ | (Matrix.of x).det ≠ 0} :=
      isOpen_ne_fun continuous_detM continuous_const
    have hp := ho.measure_pos volume ⟨(1 : Matrix (Fin m) (Fin m) ℂ), by
      show (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0
      simp⟩
    refine hp.ne' (measure_mono_null (fun x hx => ?_) h)
    intro h0
    have := wt_cancel x hx
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have left : ∀ a : Fin m → Fin m → ℂ, (Matrix.of a).det ≠ 0 →
      ∀ g : (Fin m → Fin m → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM a y) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have hm : Measurable fun y => g (mulM a y) :=
      hg.comp (measurable_mulM (measurable_const (a := a)) measurable_id')
    rw [hint _ hm, hint _ hg, lintegral_left _ ha (fun y => g y * wt y) (hg.mul measurable_wt),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    show g (mulM a y) * wt y = _ * (g (mulM a y) * wt (mulM a y))
    rw [wt_mul, mul_left_comm, ← mul_assoc _ (wt a), wt_cancel a ha, one_mul]
  have right : ∀ a : Fin m → Fin m → ℂ, (Matrix.of a).det ≠ 0 →
      ∀ g : (Fin m → Fin m → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM y a) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have hm : Measurable fun y => g (mulM y a) :=
      hg.comp (measurable_mulM measurable_id' (measurable_const (a := a)))
    rw [hint _ hm, hint _ hg, lintegral_right _ ha (fun y => g y * wt y) (hg.mul measurable_wt),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    show g (mulM y a) * wt y = _ * (g (mulM y a) * wt (mulM y a))
    rw [wt_mul, mul_left_comm, mul_comm (wt y), ← mul_assoc _ (wt a), wt_cancel a ha, one_mul]
  have hfi : Measurable fun x => f (invM x) := hf.comp measurable_invM
  rw [← hint _ hfi, ← hint _ hf]
  obtain ⟨t, ht, -, ht0, ht1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0)
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hne)
  set g : (Fin m → Fin m → ℂ) → ℝ≥0∞ := t.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator ht
  have hgi : ∫⁻ y, g y ∂μ = μ t := lintegral_indicator_one ht
  have key : (∫⁻ x, f (invM x) ∂μ) * μ t = (∫⁻ x, f x ∂μ) * μ t := by
    calc (∫⁻ x, f (invM x) ∂μ) * μ t
        = ∫⁻ x, ∫⁻ y, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          rw [← lintegral_mul_const _ hfi]
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => g (mulM x y) :=
            hg.comp (measurable_mulM measurable_const measurable_id')
          rw [lintegral_const_mul _ hm, left x hx g hg, hgi]
      _ = ∫⁻ y, ∫⁻ x, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hfi.comp measurable_fst).mul
            (hg.comp (measurable_mulM measurable_fst measurable_snd))
      _ = ∫⁻ y, ∫⁻ x, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          simp only
          rw [← right y hy (fun x => f (mulM y (invM x)) * g x)
            ((hf.comp (measurable_mulM measurable_const measurable_invM)).mul hg)]
          refine lintegral_congr fun x => ?_
          congr 2
          apply Matrix.of.injective
          rw [of_mulM, of_invM, of_invM, of_mulM, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
            Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hy), Matrix.one_mul]
      _ = ∫⁻ x, ∫⁻ y, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hf.comp (measurable_mulM measurable_fst
            (measurable_invM.comp measurable_snd))).mul (hg.comp measurable_snd)
      _ = ∫⁻ x, (∫⁻ y, f y ∂μ) * g x ∂μ := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => f (mulM y (invM x)) :=
            hf.comp (measurable_mulM measurable_id' measurable_const)
          have hx' : (Matrix.of (invM x)).det ≠ 0 :=
            (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hx)).ne_zero
          rw [lintegral_mul_const _ hm, right (invM x) hx' f hf]
      _ = (∫⁻ x, f x ∂μ) * μ t := by rw [lintegral_const_mul _ hg, hgi]
  exact (ENNReal.mul_left_inj ht0.ne' ht1.ne).mp key
end GlobalTheory.GLFirstColumn
