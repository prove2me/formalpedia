-- Prove2me | solution 1 for MultiItemRev.TwoIID.rhs12_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:00:18.471461+00:00
-- url     : https://prove2.me/submissions/b0cd9ae3-391f-4398-aa33-e7f2f803a21d

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model
import Theorems.Thm_MultiItemRev_TwoIID_zeta_le

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TwoIIDRhs

/-- The threshold `p_θ = inf {t | θ < φ t}` (as an extended real; `⊤` if the set is empty). -/
noncomputable def thr (φ : ℝ≥0 → ℝ) (θ : ℝ) : ℝ≥0∞ := ⨅ t ∈ {t : ℝ≥0 | θ < φ t}, (t : ℝ≥0∞)

theorem thr_mono (φ : ℝ≥0 → ℝ) : Monotone (thr φ) := by
  intro a b hab
  unfold thr
  apply biInf_mono
  intro t ht
  exact lt_of_le_of_lt hab ht

theorem thr_le (φ : ℝ≥0 → ℝ) {θ : ℝ} {t : ℝ≥0} (ht : θ < φ t) : thr φ θ ≤ t :=
  iInf₂_le (f := fun (t : ℝ≥0) (_ : t ∈ {t : ℝ≥0 | θ < φ t}) => (t : ℝ≥0∞)) t ht

theorem mem_of_thr_lt (φ : ℝ≥0 → ℝ) (hφ : Monotone φ) {θ : ℝ} {t : ℝ≥0}
    (h : thr φ θ < t) : θ < φ t := by
  unfold thr at h
  rw [iInf_lt_iff] at h
  obtain ⟨s, hs⟩ := h
  rw [iInf_lt_iff] at hs
  obtain ⟨hs1, hs2⟩ := hs
  have : s ≤ t := le_of_lt (by exact_mod_cast hs2)
  exact lt_of_lt_of_le hs1 (hφ this)

/-- Pointwise identity behind the layer-cake decomposition. -/
theorem per_theta (φ : ℝ≥0 → ℝ) (hφ : Monotone φ) (θ : ℝ) (y z : ℝ≥0) :
    ENNReal.ofReal ((min y z : ℝ≥0) : ℝ) * ({t : ℝ≥0 | θ < φ t}.indicator 1 y) =
      volume ({t : ℝ | θ < φ t.toNNReal} ∩ Ioc 0 ((min y z : ℝ≥0) : ℝ)) +
        ({t : ℝ≥0 | θ < φ t}.indicator 1 y) * min (z : ℝ≥0∞) (thr φ θ) := by
  set Λ := min y z with hΛ
  by_cases hy : θ < φ y
  · have hmem : y ∈ {t : ℝ≥0 | θ < φ t} := hy
    rw [indicator_of_mem hmem, Pi.one_apply, mul_one, one_mul]
    have hp := thr_le φ hy
    have hpne : thr φ θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hp
    set p := (thr φ θ).toNNReal with hpdef
    have hpe : thr φ θ = p := (ENNReal.coe_toNNReal hpne).symm
    rw [hpe] at hp ⊢
    have ha : ∀ t : ℝ≥0, θ < φ t → p ≤ t := by
      intro t ht
      have := thr_le φ ht
      rw [hpe] at this
      exact_mod_cast this
    have hb : ∀ t : ℝ≥0, p < t → θ < φ t := by
      intro t ht
      apply mem_of_thr_lt φ hφ
      rw [hpe]; exact_mod_cast ht
    have py : p ≤ y := by exact_mod_cast hp
    have hvol : volume ({t : ℝ | θ < φ t.toNNReal} ∩ Ioc 0 (Λ : ℝ)) =
        ENNReal.ofReal ((Λ : ℝ) - p) := by
      apply le_antisymm
      · calc volume ({t : ℝ | θ < φ t.toNNReal} ∩ Ioc 0 (Λ : ℝ))
            ≤ volume (Icc (p : ℝ) Λ) := by
              apply measure_mono
              rintro t ⟨ht1, ht2, ht3⟩
              simp only [mem_setOf_eq] at ht1
              have h1 := ha _ ht1
              have h2 : (p : ℝ) ≤ (t.toNNReal : ℝ) := by exact_mod_cast h1
              rw [Real.coe_toNNReal _ ht2.le] at h2
              exact ⟨h2, ht3⟩
          _ = _ := Real.volume_Icc
      · calc ENNReal.ofReal ((Λ : ℝ) - p) = volume (Ioc (p : ℝ) Λ) := Real.volume_Ioc.symm
          _ ≤ _ := by
              apply measure_mono
              rintro t ⟨ht1, ht2⟩
              have ht0 : 0 < t := lt_of_le_of_lt p.2 ht1
              refine ⟨?_, ht0, ht2⟩
              simp only [mem_setOf_eq]
              apply hb
              rw [Real.lt_toNNReal_iff_coe_lt]
              exact ht1
    rw [hvol, ← ENNReal.coe_min, ← ENNReal.ofReal_coe_nnreal]
    by_cases hzp : z ≤ p
    · have hΛz : Λ = z := by rw [hΛ]; exact min_eq_right (le_trans hzp py)
      have : ((Λ : ℝ) - p) ≤ 0 := by rw [hΛz]; simpa using hzp
      rw [ENNReal.ofReal_of_nonpos this, zero_add, min_eq_left hzp, hΛz]
    · push_neg at hzp
      have hpΛ : p ≤ Λ := le_min py hzp.le
      rw [min_eq_right hzp.le, ← ENNReal.ofReal_add (sub_nonneg.mpr (by exact_mod_cast hpΛ))
        (NNReal.coe_nonneg p)]
      congr 1
      ring
  · have hmem : y ∉ {t : ℝ≥0 | θ < φ t} := hy
    rw [indicator_of_notMem hmem, mul_zero, zero_mul, add_zero]
    symm
    rw [measure_eq_zero_iff_ae_notMem]
    apply ae_of_all
    rintro t ⟨ht1, ht2, ht3⟩
    simp only [mem_setOf_eq] at ht1
    apply hy
    apply lt_of_lt_of_le ht1
    apply hφ
    have : t ≤ y := le_trans ht3 (by exact_mod_cast min_le_left y z)
    rw [Real.toNNReal_le_iff_le_coe]
    exact this

/-- The layer-cake form of `W(y,z) = Λ φ(y) - ∫_0^Λ φ`. -/
theorem W_eq (φ : ℝ≥0 → ℝ) (hφ : Monotone φ) (hφ01 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (y z : ℝ≥0) :
    ENNReal.ofReal (((min y z : ℝ≥0) : ℝ) * φ y -
        ∫ t in (0 : ℝ)..(((min y z : ℝ≥0) : ℝ)), φ t.toNNReal) =
      ∫⁻ θ in Ioi 0, ({t : ℝ≥0 | θ < φ t}.indicator 1 y) * min (z : ℝ≥0∞) (thr φ θ) := by
  set Λ := min y z with hΛ
  have hψm : Measurable (fun t : ℝ => φ t.toNNReal) :=
    (hφ.comp (fun a b h => Real.toNNReal_le_toNNReal h)).measurable
  have hψ0 : ∀ t : ℝ, 0 ≤ φ t.toNNReal := fun t => (hφ01 _).1
  have hint := fun θ => per_theta φ hφ θ y z
  have hL : ∫⁻ θ in Ioi 0, ENNReal.ofReal (Λ : ℝ) * ({t : ℝ≥0 | θ < φ t}.indicator 1 y) =
      ENNReal.ofReal (Λ : ℝ) * ENNReal.ofReal (φ y) := by
    rw [lintegral_const_mul]
    · congr 1
      have : (fun θ : ℝ => ({t : ℝ≥0 | θ < φ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) y)) =
          (Iio (φ y)).indicator 1 := by
        funext θ
        by_cases h : θ < φ y
        · rw [indicator_of_mem (show y ∈ {t : ℝ≥0 | θ < φ t} from h),
            indicator_of_mem (show θ ∈ Iio (φ y) from h)]
          rfl
        · rw [indicator_of_notMem (show y ∉ {t : ℝ≥0 | θ < φ t} from h),
            indicator_of_notMem (show θ ∉ Iio (φ y) from h)]
      rw [this, lintegral_indicator_one measurableSet_Iio,
        Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
    · have : (fun θ : ℝ => ({t : ℝ≥0 | θ < φ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) y)) =
          (Iio (φ y)).indicator 1 := by
        funext θ
        by_cases h : θ < φ y
        · rw [indicator_of_mem (show y ∈ {t : ℝ≥0 | θ < φ t} from h),
            indicator_of_mem (show θ ∈ Iio (φ y) from h)]
          rfl
        · rw [indicator_of_notMem (show y ∉ {t : ℝ≥0 | θ < φ t} from h),
            indicator_of_notMem (show θ ∉ Iio (φ y) from h)]
      rw [this]
      exact measurable_one.indicator measurableSet_Iio
  have hV : ∫⁻ θ in Ioi 0, volume ({t : ℝ | θ < φ t.toNNReal} ∩ Ioc 0 (Λ : ℝ)) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..(Λ : ℝ), φ t.toNNReal) := by
    have e1 : ∀ θ : ℝ, volume ({t : ℝ | θ < φ t.toNNReal} ∩ Ioc 0 (Λ : ℝ)) =
        (volume.restrict (Ioc 0 (Λ : ℝ))) {t : ℝ | θ < φ t.toNNReal} := by
      intro θ
      rw [Measure.restrict_apply' measurableSet_Ioc]
    simp_rw [e1]
    rw [← lintegral_eq_lintegral_meas_lt _ (ae_of_all _ hψ0) hψm.aemeasurable,
      intervalIntegral.integral_of_le (NNReal.coe_nonneg Λ)]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine Measure.integrableOn_of_bounded (M := 1) ?_ hψm.aestronglyMeasurable ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
      · apply ae_of_all
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 t)]
        exact (hφ01 _).2
    · exact ae_of_all _ hψ0
  have hVm : Measurable (fun θ : ℝ => volume ({t : ℝ | θ < φ t.toNNReal} ∩ Ioc 0 (Λ : ℝ))) := by
    apply Antitone.measurable
    intro a b hab
    apply measure_mono
    rintro t ⟨ht1, ht2⟩
    exact ⟨lt_of_le_of_lt hab ht1, ht2⟩
  have key : ENNReal.ofReal (Λ : ℝ) * ENNReal.ofReal (φ y) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..(Λ : ℝ), φ t.toNNReal) +
        ∫⁻ θ in Ioi 0, ({t : ℝ≥0 | θ < φ t}.indicator 1 y) * min (z : ℝ≥0∞) (thr φ θ) := by
    rw [← hL, ← hV, ← lintegral_add_left hVm]
    apply lintegral_congr
    intro θ
    exact hint θ
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..(Λ : ℝ), φ t.toNNReal :=
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg Λ) (fun t _ => hψ0 t)
  rw [ENNReal.ofReal_sub _ hI0, ENNReal.ofReal_mul (NNReal.coe_nonneg Λ), key,
    ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]

end TwoIIDRhs

theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) (φ : ℝ≥0 → ℝ)
    (hφ : Monotone φ) (hφ01 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) :
    let μ := Measure.pi (fun _ : Fin 2 => ν)
    let r := (MultiItemRev.Decomp.Rev1 ν).toReal
    ((2 * r - 2 * r * ∫ t, φ t ∂ν : ℝ) : EReal) +
      2 * ((∫⁻ x, ENNReal.ofReal
        (((min (x 0) (x 1) : ℝ≥0) : ℝ) * φ (x 0) -
          ∫ t in (0 : ℝ)..(((min (x 0) (x 1) : ℝ≥0) : ℝ)), φ t.toNNReal) ∂μ : ℝ≥0∞) : EReal) ≤
        ((2 * r * (1 + 1 / Real.exp 1) : ℝ) : EReal) := by
  intro μ r
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hφm : Measurable φ := hφ.measurable
  set F : (Fin 2 → ℝ≥0) → ℝ → ℝ≥0∞ := fun x θ =>
    ({t : ℝ≥0 | θ < φ t}.indicator 1 (x 0)) * min ((x 1 : ℝ≥0∞)) (TwoIIDRhs.thr φ θ) with hF
  have hF_meas : Measurable (Function.uncurry F) := by
    have e : Function.uncurry F = fun q : (Fin 2 → ℝ≥0) × ℝ =>
        ({q : (Fin 2 → ℝ≥0) × ℝ | q.2 < φ (q.1 0)}.indicator 1 q) *
          min ((q.1 1 : ℝ≥0∞)) (TwoIIDRhs.thr φ q.2) := by
      funext q
      simp only [Function.uncurry, hF]
      congr 1
    rw [e]
    apply Measurable.mul
    · apply measurable_one.indicator
      exact measurableSet_lt measurable_snd
        (hφm.comp ((measurable_pi_apply 0).comp measurable_fst))
    · exact (measurable_coe_nnreal_ennreal.comp ((measurable_pi_apply 1).comp measurable_fst)).min
        ((TwoIIDRhs.thr_mono φ).measurable.comp measurable_snd)
  set I := ∫⁻ x, ENNReal.ofReal (((min (x 0) (x 1) : ℝ≥0) : ℝ) * φ (x 0) -
          ∫ t in (0 : ℝ)..(((min (x 0) (x 1) : ℝ≥0) : ℝ)), φ t.toNNReal) ∂μ with hI
  have hI1 : I = ∫⁻ θ in Ioi 0, ∫⁻ x, F x θ ∂μ := by
    rw [hI]
    simp_rw [TwoIIDRhs.W_eq φ hφ hφ01]
    exact lintegral_lintegral_swap hF_meas.aemeasurable
  have hinner : ∀ θ, ∫⁻ x, F x θ ∂μ =
      ν {t | θ < φ t} * ∫⁻ z, min (z : ℝ≥0∞) (TwoIIDRhs.thr φ θ) ∂ν := by
    intro θ
    have hmp := measurePreserving_finTwoArrow ν
    have hS : MeasurableSet {t : ℝ≥0 | θ < φ t} := measurableSet_lt measurable_const hφm
    calc ∫⁻ x, F x θ ∂μ = ∫⁻ q, ({t : ℝ≥0 | θ < φ t}.indicator 1 q.1) *
            min ((q.2 : ℝ≥0∞)) (TwoIIDRhs.thr φ θ) ∂(ν.prod ν) := by
          rw [← hmp.map_eq, lintegral_map_equiv]; rfl
      _ = (∫⁻ y, {t : ℝ≥0 | θ < φ t}.indicator 1 y ∂ν) *
            ∫⁻ z, min (z : ℝ≥0∞) (TwoIIDRhs.thr φ θ) ∂ν :=
          lintegral_prod_mul (measurable_one.indicator hS).aemeasurable
            (measurable_coe_nnreal_ennreal.min measurable_const).aemeasurable
      _ = _ := by rw [lintegral_indicator_one hS]
  have hbound : ∀ θ, ν {t | θ < φ t} * ∫⁻ z, min (z : ℝ≥0∞) (TwoIIDRhs.thr φ θ) ∂ν ≤
      ENNReal.ofReal r * ν {t | θ < φ t} +
        (Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal (r / Real.exp 1)) θ := by
    intro θ
    by_cases hne : ({t : ℝ≥0 | θ < φ t}).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp hne]; simp
    obtain ⟨y, hy⟩ := hne
    have hθ1 : θ < 1 := lt_of_lt_of_le hy (hφ01 y).2
    rw [indicator_of_mem (show θ ∈ Iio (1 : ℝ) from hθ1)]
    have hp := TwoIIDRhs.thr_le φ hy
    have hpne : TwoIIDRhs.thr φ θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hp
    set p := (TwoIIDRhs.thr φ θ).toNNReal with hpdef
    have hpe : TwoIIDRhs.thr φ θ = p := (ENNReal.coe_toNNReal hpne).symm
    rw [hpe]
    have hSG : ν {t | θ < φ t} ≤ ν {t | p ≤ t} := by
      apply measure_mono
      intro t ht
      have := TwoIIDRhs.thr_le φ ht
      rw [hpe] at this
      exact_mod_cast this
    have hminm : Measurable (fun t : ℝ≥0 => ((min t p : ℝ≥0) : ℝ)) :=
      (measurable_id.min measurable_const).coe_nnreal_real
    have hm : ∫⁻ z, min (z : ℝ≥0∞) (p : ℝ≥0∞) ∂ν =
        ENNReal.ofReal (∫ t, ((min t p : ℝ≥0) : ℝ) ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal]
      · apply lintegral_congr
        intro z
        rw [← ENNReal.coe_min, ENNReal.ofReal_coe_nnreal]
      · refine Integrable.mono' (integrable_const (p : ℝ)) hminm.aestronglyMeasurable ?_
        apply ae_of_all
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        exact_mod_cast min_le_right t p
      · exact ae_of_all _ (fun _ => NNReal.coe_nonneg _)
    rw [hm]
    set m := ∫ t, ((min t p : ℝ≥0) : ℝ) ∂ν with hmdef
    have hz : (ν {t | p ≤ t}).toReal * (m - r) ≤ r / Real.exp 1 :=
      MultiItemRev.TwoIID.zeta_le ν hr p
    set S := ν {t | θ < φ t} with hSdef
    set G := ν {t | p ≤ t} with hGdef
    have hSne : S ≠ ⊤ := measure_ne_top _ _
    have hGne : G ≠ ⊤ := measure_ne_top _ _
    have hsg : S.toReal ≤ G.toReal := ENNReal.toReal_mono hGne hSG
    have hs0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    have hreal : S.toReal * m ≤ r * S.toReal + r / Real.exp 1 := by
      have hre : 0 ≤ r / Real.exp 1 := div_nonneg hr0 he.le
      by_cases hmr : m ≤ r
      · have := mul_le_mul_of_nonneg_left hmr hs0
        linarith
      · push_neg at hmr
        have : S.toReal * (m - r) ≤ G.toReal * (m - r) :=
          mul_le_mul_of_nonneg_right hsg (by linarith)
        nlinarith
    rw [← ENNReal.ofReal_toReal hSne, ← ENNReal.ofReal_mul hs0, ← ENNReal.ofReal_mul hr0,
      ← ENNReal.ofReal_add (mul_nonneg hr0 hs0) (div_nonneg hr0 he.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hint0 : 0 ≤ ∫ t, φ t ∂ν := integral_nonneg (fun t => (hφ01 t).1)
  have hlayer : ∫⁻ θ in Ioi 0, ν {t | θ < φ t} = ENNReal.ofReal (∫ t, φ t ∂ν) := by
    rw [← lintegral_eq_lintegral_meas_lt ν (ae_of_all _ (fun t => (hφ01 t).1)) hφm.aemeasurable]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine Integrable.mono' (integrable_const (1 : ℝ)) hφm.aestronglyMeasurable ?_
      apply ae_of_all
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 t).1]
      exact (hφ01 t).2
    · exact ae_of_all _ (fun t => (hφ01 t).1)
  have hSmeas : Measurable (fun θ : ℝ => ν {t | θ < φ t}) :=
    Antitone.measurable (fun a b hab => measure_mono (fun t ht => lt_of_le_of_lt hab ht))
  have hIle : I ≤ ENNReal.ofReal (r * ∫ t, φ t ∂ν + r / Real.exp 1) := by
    rw [hI1]
    calc ∫⁻ θ in Ioi 0, ∫⁻ x, F x θ ∂μ
        ≤ ∫⁻ θ in Ioi 0, (ENNReal.ofReal r * ν {t | θ < φ t} +
            (Iio (1 : ℝ)).indicator (fun _ => ENNReal.ofReal (r / Real.exp 1)) θ) := by
          apply lintegral_mono
          intro θ
          simp only
          rw [hinner]
          exact hbound θ
      _ = ENNReal.ofReal r * ENNReal.ofReal (∫ t, φ t ∂ν) + ENNReal.ofReal (r / Real.exp 1) := by
          rw [lintegral_add_left (hSmeas.const_mul _), lintegral_const_mul _ hSmeas, hlayer,
            lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
            Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
      _ = _ := by
          rw [← ENNReal.ofReal_mul hr0,
            ← ENNReal.ofReal_add (mul_nonneg hr0 hint0) (div_nonneg hr0 he.le)]
  have hK0 : 0 ≤ r * ∫ t, φ t ∂ν + r / Real.exp 1 :=
    add_nonneg (mul_nonneg hr0 hint0) (div_nonneg hr0 he.le)
  calc ((2 * r - 2 * r * ∫ t, φ t ∂ν : ℝ) : EReal) + 2 * (I : EReal)
      ≤ ((2 * r - 2 * r * ∫ t, φ t ∂ν : ℝ) : EReal) +
          2 * ((ENNReal.ofReal (r * ∫ t, φ t ∂ν + r / Real.exp 1) : ℝ≥0∞) : EReal) := by
        gcongr
        exact_mod_cast hIle
    _ = ((2 * r - 2 * r * ∫ t, φ t ∂ν + 2 * (r * ∫ t, φ t ∂ν + r / Real.exp 1) : ℝ) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left hK0]
        norm_cast
    _ ≤ _ := by
        apply EReal.coe_le_coe_iff.mpr
        apply le_of_eq
        ring
