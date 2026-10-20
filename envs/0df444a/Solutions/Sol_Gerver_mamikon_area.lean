-- Prove2me | solution 1 for Gerver.mamikon_area
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:29:40.023083+00:00
-- url     : https://prove2.me/submissions/d0ea0193-154f-4bdb-9e56-7d8238c8b956

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

open MeasureTheory Set

namespace Gerver

/-- the derivative matrix of (t, r) ↦ z t + r v t -/
noncomputable def maD (w : ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![w.1 - p.2 * Real.cos p.1, -Real.sin p.1;
       w.2 - p.2 * Real.sin p.1, Real.cos p.1]).toContinuousLinearMap

lemma maD_det (w : ℝ × ℝ) (p : ℝ × ℝ) (hw : dot w (u p.1) = 0) : (maD w p).det = -p.2 := by
  unfold maD
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  simp only [dot, u] at hw
  have := Real.cos_sq_add_sin_sq p.1
  linear_combination hw - p.2 * this

lemma ma_hasFDeriv (z : ℝ → ℝ × ℝ) (w : ℝ × ℝ) (p : ℝ × ℝ) (hz : HasDerivAt z w p.1) :
    HasFDerivAt (fun q : ℝ × ℝ => z q.1 + scale q.2 (v q.1)) (maD w p) p := by
  unfold maD
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hz1 : HasDerivAt (fun t => (z t).1) w.1 p.1 := hz.fst
  have hz2 : HasDerivAt (fun t => (z t).2) w.2 p.1 := hz.snd
  have h1a := hz1.comp_hasFDerivAt p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h1b := hz2.comp_hasFDerivAt p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hs := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).mul ((Real.hasDerivAt_sin p.1).comp_hasFDerivAt p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))
  have hc := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).mul ((Real.hasDerivAt_cos p.1).comp_hasFDerivAt p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))
  have e : (fun q : ℝ × ℝ => z q.1 + scale q.2 (v q.1)) =
      fun q => ((z q.1).1 - q.2 * Real.sin q.1, (z q.1).2 + q.2 * Real.cos q.1) := by
    ext q <;> simp [scale, v] <;> ring
  rw [e]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ) (h1a.sub hs) (h1b.add hc) using 2 <;>
  ext <;> simp <;> ring

lemma ma_inner (c : ℝ) :
    ∫⁻ r in Ioo (min 0 c) (max 0 c), ENNReal.ofReal |r| = ENNReal.ofReal (c ^ 2 / 2) := by
  have hle : min 0 c ≤ max 0 c := min_le_max
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle]
    rcases le_total 0 c with hc | hc
    · rw [min_eq_left hc, max_eq_right hc]
      rw [intervalIntegral.integral_congr (g := fun r => r) (fun r hr => by
        rw [uIcc_of_le hc] at hr; exact abs_of_nonneg hr.1)]
      simp [integral_id]
    · rw [min_eq_right hc, max_eq_left hc]
      rw [intervalIntegral.integral_congr (g := fun r => -r) (fun r hr => by
        rw [uIcc_of_le hc] at hr; exact abs_of_nonpos hr.2)]
      rw [intervalIntegral.integral_neg, integral_id]; ring
  · exact (continuous_abs.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · exact Filter.Eventually.of_forall fun r => abs_nonneg r

lemma ma_graph_null {a b : ℝ} (α : ℝ → ℝ) (hα : ContinuousOn α (Icc a b)) :
    vol2 ((fun t => (t, α t)) '' Icc a b) = 0 := by
  have hc : IsCompact ((fun t => (t, α t)) '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hα)
  rw [vol2, Measure.prod_apply hc.isClosed.measurableSet]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun t => ?_)
  refine measure_mono_null (t := {α t}) ?_ (measure_singleton _)
  rintro r ⟨t', _, ht'⟩
  simp only [Prod.mk.injEq] at ht'
  obtain ⟨rfl, rfl⟩ := ht'
  rfl

lemma ma_ne {c r : ℝ} (h : r ∈ Ioo (min 0 c) (max 0 c)) : c ≠ 0 := by
  rintro rfl; simp at h

lemma ma_div1 {c r : ℝ} (h : r ∈ Ioo (min 0 c) (max 0 c)) : r / c ∈ Ioo 0 1 := by
  have hc := ma_ne h
  rcases lt_or_gt_of_ne hc with hc | hc
  · rw [min_eq_right hc.le, max_eq_left hc.le] at h
    exact ⟨div_pos_of_neg_of_neg h.2 hc, (div_lt_one_of_neg hc).2 h.1⟩
  · rw [min_eq_left hc.le, max_eq_right hc.le] at h
    exact ⟨div_pos h.1 hc, (div_lt_one hc).2 h.2⟩

lemma ma_div2 {c s : ℝ} (hc : c ≠ 0) (hs : s ∈ Ioo (0:ℝ) 1) : s * c ∈ Ioo (min 0 c) (max 0 c) := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · rw [min_eq_right hc.le, max_eq_left hc.le]
    constructor <;> nlinarith [hs.1, hs.2]
  · rw [min_eq_left hc.le, max_eq_right hc.le]
    constructor <;> nlinarith [hs.1, hs.2]

lemma ma_scale_diff : Differentiable ℝ (fun q : ℝ × ℝ => scale q.2 (v q.1)) := by
  unfold scale v
  fun_prop

end Gerver

open Gerver in
theorem solution (z : ℝ → ℝ × ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (hab : a < b) (hb : b < a + Real.pi)
    (hz : ContDiffOn ℝ 1 z (Set.Icc a b)) (hα : ContinuousOn α (Set.Icc a b))
    (htan : ∀ t ∈ Set.Ioo a b, dot (derivWithin z (Set.Icc a b) t) (u t) = 0)
    (hinj : ∀ t ∈ Set.Ioo a b, ∀ s ∈ Set.Ioo 0 1, ∀ t' ∈ Set.Ioo a b,
      ∀ s' ∈ Set.Ioo 0 1,
      z t + scale (s * α t) (v t) = z t' + scale (s' * α t') (v t') →
        t = t' ∧ s = s') :
    area (swept z α a b) = ∫ t in a..b, α t ^ 2 / 2 := by
  set F : ℝ × ℝ → ℝ × ℝ := fun q => z q.1 + scale q.2 (v q.1) with hF
  set D : Set (ℝ × ℝ) := {p | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo (min 0 (α p.1)) (max 0 (α p.1))} with hD
  have hv : vol2 = (volume : Measure (ℝ × ℝ)) := rfl
  have hzd : DifferentiableOn ℝ z (Icc a b) := hz.differentiableOn one_ne_zero
  -- D is open
  have hDopen : IsOpen D := by
    have hc : ContinuousOn (fun q : ℝ × ℝ => (q.2 - min 0 (α q.1), max 0 (α q.1) - q.2))
        (Ioo a b ×ˢ univ) := by
      have h1 : ContinuousOn (fun q : ℝ × ℝ => α q.1) (Ioo a b ×ˢ univ) :=
        (hα.mono Ioo_subset_Icc_self).comp continuousOn_fst (fun q hq => hq.1)
      exact (continuousOn_snd.sub (ContinuousOn.inf continuousOn_const h1)).prodMk
        ((ContinuousOn.sup continuousOn_const h1).sub continuousOn_snd)
    convert hc.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_univ) ((isOpen_Ioi (a := (0:ℝ))).prod (isOpen_Ioi (a := (0:ℝ))))
      using 1
    ext q
    simp only [hD, mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage,
      mem_Ioi, sub_pos, mem_Ioo]
  have hDm : MeasurableSet D := hDopen.measurableSet
  -- derivative
  have hder : ∀ p ∈ D, HasFDerivWithinAt F (maD (derivWithin z (Icc a b) p.1) p) D p := by
    intro p hp
    have hn : Icc a b ∈ nhds p.1 := Icc_mem_nhds hp.1.1 hp.1.2
    have hd : HasDerivAt z (derivWithin z (Icc a b) p.1) p.1 := by
      rw [derivWithin_of_mem_nhds hn]
      exact ((hzd p.1 (Ioo_subset_Icc_self hp.1)).differentiableAt hn).hasDerivAt
    exact (ma_hasFDeriv z _ p hd).hasFDerivWithinAt
  -- injectivity
  have hinjD : InjOn F D := by
    intro p hp q hq hpq
    have hp0 := ma_ne hp.2
    have hq0 := ma_ne hq.2
    have e1 : p.2 / α p.1 * α p.1 = p.2 := div_mul_cancel₀ _ hp0
    have e2 : q.2 / α q.1 * α q.1 = q.2 := div_mul_cancel₀ _ hq0
    have key := hinj p.1 hp.1 _ (ma_div1 hp.2) q.1 hq.1 _ (ma_div1 hq.2)
      (by rw [e1, e2]; exact hpq)
    have h2 : p.2 = q.2 := by
      calc p.2 = p.2 / α p.1 * α p.1 := e1.symm
        _ = q.2 / α q.1 * α q.1 := by rw [key.2, key.1]
        _ = q.2 := e2
    exact Prod.ext key.1 h2
  have hcv := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (ℝ × ℝ)) hDm hder hinjD
  have hdet : ∀ p ∈ D, ENNReal.ofReal |(maD (derivWithin z (Icc a b) p.1) p).det| =
      ENNReal.ofReal |p.2| := by
    intro p hp
    rw [maD_det _ _ (htan p.1 hp.1), abs_neg]
  rw [setLIntegral_congr_fun hDm hdet] at hcv
  -- compute the integral
  have hint : ∫⁻ p in D, ENNReal.ofReal |p.2| ∂(volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (∫ t in a..b, α t ^ 2 / 2) := by
    rw [← lintegral_indicator hDm, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      lintegral_prod _ ((Measurable.ennreal_ofReal (measurable_snd.abs)).indicator hDm).aemeasurable]
    have hin : ∀ t : ℝ, ∫⁻ r, D.indicator (fun p : ℝ × ℝ => ENNReal.ofReal |p.2|) (t, r) =
        (Ioo a b).indicator (fun t => ENNReal.ofReal (α t ^ 2 / 2)) t := by
      intro t
      by_cases ht : t ∈ Ioo a b
      · rw [indicator_of_mem ht, ← ma_inner (α t), ← lintegral_indicator measurableSet_Ioo]
        congr 1
        ext r
        simp only [indicator, hD, mem_setOf_eq, ht, true_and]
      · rw [indicator_of_notMem ht]
        have : ∀ r : ℝ, (t, r) ∉ D := fun r hr => ht hr.1
        simp [indicator_of_notMem (this _)]
    simp_rw [hin]
    rw [lintegral_indicator measurableSet_Ioo, ← ofReal_integral_eq_lintegral_ofReal,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    · exact ((hα.pow 2).div_const 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · exact Filter.Eventually.of_forall fun t => by positivity
  -- swept vs image
  have hsw : vol2 (swept z α a b) = vol2 (F '' D) := by
    set G : Set (ℝ × ℝ) := (fun t => (t, α t)) '' Icc a b with hG
    set N : Set (ℝ × ℝ) := (({a, b} : Set ℝ) ×ˢ univ ∪ Icc a b ×ˢ {0}) ∪ G with hN
    have hN0 : vol2 N = 0 := by
      refine measure_union_null (measure_union_null ?_ ?_) (ma_graph_null α hα)
      · rw [vol2, Measure.prod_prod, (Set.toFinite ({a, b} : Set ℝ)).measure_zero, zero_mul]
      · rw [vol2, Measure.prod_prod, Real.volume_singleton, mul_zero]
    have hNsub : N ⊆ Icc a b ×ˢ univ := by
      rintro p ((⟨hp, -⟩ | ⟨hp, -⟩) | ⟨t, ht, rfl⟩)
      · have : p.1 = a ∨ p.1 = b := by simpa using hp
        rcases this with h | h <;> exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
      · exact ⟨hp, mem_univ _⟩
      · exact ⟨ht, mem_univ _⟩
    have hFd : DifferentiableOn ℝ F (Icc a b ×ˢ univ) :=
      (hzd.comp differentiableOn_fst (fun q hq => hq.1)).add ma_scale_diff.differentiableOn
    have hFN : vol2 (F '' N) = 0 := by
      rw [hv] at hN0 ⊢
      exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (hFd.mono hNsub) hN0
    have h1 : F '' D ⊆ swept z α a b := by
      rintro _ ⟨p, hp, rfl⟩
      simp only [swept, mem_iUnion]
      have hs := ma_div1 hp.2
      refine ⟨p.1, Ioo_subset_Icc_self hp.1, p.2 / α p.1, Ioo_subset_Icc_self hs, ?_⟩
      simp only [hF, div_mul_cancel₀ _ (ma_ne hp.2)]
    have h2 : swept z α a b ⊆ F '' D ∪ F '' N := by
      intro q hq
      simp only [swept, mem_iUnion, mem_setOf_eq] at hq
      obtain ⟨t, ht, s, hs, rfl⟩ := hq
      by_cases hta : t = a ∨ t = b
      · right
        exact ⟨(t, s * α t), Or.inl (Or.inl ⟨by rcases hta with h | h <;> simp [h], mem_univ _⟩), rfl⟩
      by_cases hs0 : s = 0 ∨ α t = 0
      · right
        refine ⟨(t, 0), Or.inl (Or.inr ⟨ht, rfl⟩), ?_⟩
        rcases hs0 with h | h <;> simp [hF, h]
      by_cases hs1 : s = 1
      · right
        exact ⟨(t, α t), Or.inr ⟨t, ht, rfl⟩, by simp [hF, hs1]⟩
      left
      push Not at hta hs0
      have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta.1), lt_of_le_of_ne ht.2 hta.2⟩
      have hs' : s ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0.1), lt_of_le_of_ne hs.2 hs1⟩
      exact ⟨(t, s * α t), ⟨ht', ma_div2 hs0.2 hs'⟩, rfl⟩
    refine le_antisymm ?_ (measure_mono h1)
    calc vol2 (swept z α a b) ≤ vol2 (F '' D ∪ F '' N) := measure_mono h2
      _ ≤ vol2 (F '' D) + vol2 (F '' N) := measure_union_le _ _
      _ = vol2 (F '' D) := by rw [hFN, add_zero]
  have hnn : 0 ≤ ∫ t in a..b, α t ^ 2 / 2 :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => by positivity)
  unfold area
  rw [hsw, hv, ← hcv, hint, ENNReal.toReal_ofReal hnn]
