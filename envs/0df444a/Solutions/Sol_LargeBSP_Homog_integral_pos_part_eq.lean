-- Prove2me | solution 1 for LargeBSP.Homog.integral_pos_part_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:43:23.904646+00:00
-- url     : https://prove2.me/submissions/0cd4e18e-64c2-4fe7-ae7a-a45eb6dc5ce4

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false



namespace BSPAux
open LargeBSP.Homog

section Quantile
variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma cdf_eq_zero_of_neg (hν0 : ν (Set.Iio 0) = 0) {y : ℝ} (hy : y < 0) : cdf ν y = 0 := by
  have h1 := ofReal_cdf ν y
  have : ν (Set.Iic y) = 0 := measure_mono_null (Set.Iic_subset_Iio.2 hy) hν0
  rw [this] at h1
  have := cdf_nonneg ν y
  have := ENNReal.ofReal_eq_zero.1 h1
  linarith

lemma qset_nonempty {u : ℝ} (hu : u < 1) : {y : ℝ | 0 ≤ y ∧ u ≤ cdf ν y}.Nonempty := by
  have h := (tendsto_cdf_atTop ν).eventually_const_lt hu
  obtain ⟨y, hy⟩ := (h.and (eventually_ge_atTop 0)).exists
  exact ⟨y, hy.2, hy.1.le⟩

lemma qset_bdd (u : ℝ) : BddBelow {y : ℝ | 0 ≤ y ∧ u ≤ cdf ν y} := ⟨0, fun y hy => hy.1⟩

lemma quantile_nonneg (F : ℝ → ℝ) (u : ℝ) : 0 ≤ quantile F u :=
  Real.sInf_nonneg (fun y hy => hy.1)

lemma le_cdf_quantile {u : ℝ} (hu1 : u < 1) : u ≤ cdf ν (quantile (cdf ν) u) := by
  set q := quantile (cdf ν) u with hq
  by_contra hlt
  push Not at hlt
  have hcont := (cdf ν).right_continuous q
  have hev : ∀ᶠ z in 𝓝[Set.Ici q] q, cdf ν z < u := hcont.tendsto.eventually (eventually_lt_nhds hlt)
  obtain ⟨b, hb, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  obtain ⟨z, hz, hzb⟩ := exists_lt_of_csInf_lt (qset_nonempty hu1) (show q < b from hb)
  have hqz : q ≤ z := csInf_le (qset_bdd u) hz
  have := hsub ⟨hqz, hzb⟩
  exact absurd hz.2 (not_le.2 this)

lemma quantile_le_iff (hν0 : ν (Set.Iio 0) = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (y : ℝ) :
    quantile (cdf ν) u ≤ y ↔ u ≤ cdf ν y := by
  constructor
  · intro h; exact le_trans (le_cdf_quantile hu1) (monotone_cdf ν h)
  · intro h
    have hy : 0 ≤ y := by
      by_contra hy; push Not at hy
      rw [cdf_eq_zero_of_neg hν0 hy] at h; linarith
    exact csInf_le (qset_bdd u) ⟨hy, h⟩

lemma lt_quantile_iff (hν0 : ν (Set.Iio 0) = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (y : ℝ) :
    y < quantile (cdf ν) u ↔ cdf ν y < u := by
  rw [← not_le, quantile_le_iff hν0 hu0 hu1, not_le]

lemma quantile_monotoneOn (hν0 : ν (Set.Iio 0) = 0) :
    MonotoneOn (quantile (cdf ν)) (Set.Ioo 0 1) := by
  intro u hu v hv huv
  rw [quantile_le_iff hν0 hu.1 hu.2]
  exact le_trans huv (le_cdf_quantile hv.2)

lemma quantile_aemeasurable (hν0 : ν (Set.Iio 0) = 0) :
    AEMeasurable (quantile (cdf ν)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monotoneOn hν0)

lemma volume_Ioo_inter_Iic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic a) = ENNReal.ofReal a := by
  apply le_antisymm
  · calc volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic a) ≤ volume (Set.Icc 0 a) := by
          apply measure_mono; intro u hu; exact ⟨hu.1.1.le, hu.2⟩
      _ = ENNReal.ofReal a := by rw [Real.volume_Icc, sub_zero]
  · calc ENNReal.ofReal a = volume (Set.Ioo 0 a) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ _ := by
          apply measure_mono; intro u hu
          exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 ha1⟩, hu.2.le⟩

/-- The quantile transform: the law of `F⁻¹(U)`, `U` uniform on `(0,1)`, is `ν`. -/
lemma map_quantile (hν0 : ν (Set.Iio 0) = 0) :
    Measure.map (quantile (cdf ν)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) = ν := by
  symm
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply_of_aemeasurable (quantile_aemeasurable hν0) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo]
  have hset : quantile (cdf ν) ⁻¹' Set.Iic y ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic (cdf ν y) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (quantile_le_iff hν0 h2.1 h2.2 y).1 h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(quantile_le_iff hν0 h2.1 h2.2 y).2 h1, h2⟩
  rw [hset, volume_Ioo_inter_Iic (cdf_nonneg ν y) (cdf_le_one ν y), ofReal_cdf]

lemma integral_eq_quantile (hν0 : ν (Set.Iio 0) = 0) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂ν = ∫ u in Set.Ioo (0 : ℝ) 1, f (quantile (cdf ν) u) := by
  conv_lhs => rw [← map_quantile hν0]
  exact integral_map (quantile_aemeasurable hν0) hf.aestronglyMeasurable

lemma integrable_quantile_iff (hν0 : ν (Set.Iio 0) = 0) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f ν ↔ IntegrableOn (fun u => f (quantile (cdf ν) u)) (Set.Ioo (0 : ℝ) 1) := by
  conv_lhs => rw [← map_quantile hν0]
  exact integrable_map_measure hf.aestronglyMeasurable (quantile_aemeasurable hν0)

lemma quantile_intervalIntegrable (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) :
    IntervalIntegrable (quantile (cdf ν)) volume 0 1 := by
  have h := (integrable_quantile_iff hν0 continuous_id).1 hν1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact h

lemma quantile_intervalIntegrable' (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (quantile (cdf ν)) volume a b := by
  apply (quantile_intervalIntegrable hν0 hν1).mono_set
  rw [Set.uIcc_of_le zero_le_one]
  intro u hu
  rcases le_total a b with h | h
  · rw [Set.uIcc_of_le h] at hu; exact ⟨le_trans ha.1 hu.1, le_trans hu.2 hb.2⟩
  · rw [Set.uIcc_of_ge h] at hu; exact ⟨le_trans hb.1 hu.1, le_trans hu.2 ha.2⟩

/-- `∫ g dν` as an interval integral of `g ∘ F⁻¹` over `[0,1]`. -/
lemma integral_eq_quantile' (hν0 : ν (Set.Iio 0) = 0) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂ν = ∫ u in (0 : ℝ)..1, f (quantile (cdf ν) u) := by
  rw [integral_eq_quantile hν0 hf, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

lemma Vlim_eq (t : ℝ) : Vlim ν t = ∫ u in (1 - t)..1, quantile (cdf ν) u := by
  unfold Vlim
  rw [intervalIntegral.integral_comp_sub_left (fun u => quantile (cdf ν) u) 1, sub_zero]

/-- `G(y) = E (X - y)^+`. -/
noncomputable def G (ν : Measure ℝ) (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂ν

lemma G_eq (hν0 : ν (Set.Iio 0) = 0) (y : ℝ) :
    G ν y = ∫ u in (0 : ℝ)..1, max (quantile (cdf ν) u - y) 0 :=
  integral_eq_quantile' hν0 (f := fun x => max (x - y) 0) (by fun_prop)

lemma posPart_intervalIntegrable (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (y : ℝ)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => max (quantile (cdf ν) u - y) 0) volume a b := by
  have h := quantile_intervalIntegrable' hν0 hν1 ha hb
  have h2 := h.sub (intervalIntegrable_const (c := y))
  exact ⟨Integrable.pos_part h2.1, Integrable.pos_part h2.2⟩

/-- `V̄(t) ≤ t y + G(y)` for every `t ∈ [0,1]` and every `y`. -/
lemma Vlim_le (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) : Vlim ν t ≤ t * y + G ν y := by
  have ha : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [G_eq hν0, Vlim_eq,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 - t)
      (posPart_intervalIntegrable hν0 hν1 y h0 ha) (posPart_intervalIntegrable hν0 hν1 y ha h1)]
  have hA : 0 ≤ ∫ u in (0 : ℝ)..(1 - t), max (quantile (cdf ν) u - y) 0 :=
    intervalIntegral.integral_nonneg ha.1 (fun u _ => le_max_right _ _)
  have hB : ∫ u in (1 - t)..1, (quantile (cdf ν) u - y) ≤
      ∫ u in (1 - t)..1, max (quantile (cdf ν) u - y) 0 :=
    intervalIntegral.integral_mono_on (by linarith [ht.1])
      ((quantile_intervalIntegrable' hν0 hν1 ha h1).sub intervalIntegrable_const)
      (posPart_intervalIntegrable hν0 hν1 y ha h1) (fun u _ => le_max_left _ _)
  rw [intervalIntegral.integral_sub (quantile_intervalIntegrable' hν0 hν1 ha h1)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at hB
  have : (1 - (1 - t)) * y = t * y := by ring
  linarith

/-- Splitting lemma: if `F⁻¹ ≤ y` below `a` and `F⁻¹ ≥ y` above `a`, then
`G(y) = V̄(1 - a) - (1 - a) y`. -/
lemma G_eq_split (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {a y : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u < a → quantile (cdf ν) u ≤ y)
    (hhi : ∀ u ∈ Set.Ioo (0 : ℝ) 1, a < u → y ≤ quantile (cdf ν) u) :
    G ν y = Vlim ν (1 - a) - (1 - a) * y := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [G_eq hν0, Vlim_eq, sub_sub_cancel,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (posPart_intervalIntegrable hν0 hν1 y h0 ha) (posPart_intervalIntegrable hν0 hν1 y ha h1)]
  have hA : ∫ u in (0 : ℝ)..a, max (quantile (cdf ν) u - y) 0 = 0 := by
    rw [intervalIntegral.integral_of_le ha.1, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu.1, lt_of_lt_of_le hu.2 ha.2⟩
      simp only
      exact max_eq_right (by linarith [hlo u hu' hu.2])
  have hB : ∫ u in a..1, max (quantile (cdf ν) u - y) 0 =
      ∫ u in a..1, (quantile (cdf ν) u - y) := by
    rw [intervalIntegral.integral_of_le ha.2, intervalIntegral.integral_of_le ha.2,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha.1 hu.1, hu.2⟩
    exact max_eq_left (by linarith [hhi u hu' hu.1])
  rw [hA, hB, zero_add, intervalIntegral.integral_sub (quantile_intervalIntegrable' hν0 hν1 ha h1)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]

/-- For `t ∈ (0,1]` there is `y ≥ 0` with `V̄(t) = t y + G(y)`. -/
lemma Vlim_eq_exists (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) : ∃ y, 0 ≤ y ∧ Vlim ν t = t * y + G ν y := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    refine ⟨0, le_rfl, ?_⟩
    have := G_eq_split hν0 hν1 (a := 0) (y := 0) ⟨le_rfl, zero_le_one⟩
      (fun u hu hu0 => absurd hu.1 (not_lt.2 hu0.le))
      (fun u hu _ => quantile_nonneg _ u)
    rw [this]; simp
  · refine ⟨quantile (cdf ν) (1 - t), quantile_nonneg _ _, ?_⟩
    have hm : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.1]⟩
    have := G_eq_split hν0 hν1 (a := 1 - t) (y := quantile (cdf ν) (1 - t))
      ⟨hm.1.le, hm.2.le⟩
      (fun u hu hlt => quantile_monotoneOn hν0 hu hm hlt.le)
      (fun u hu hlt => quantile_monotoneOn hν0 hm hu hlt.le)
    rw [this, sub_sub_cancel]; ring

end Quantile
end BSPAux




namespace BSPAux
open LargeBSP.Homog

section Tstar
variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma tstar_mem (c : ℝ) : tstar ν c ∈ Set.Icc (0 : ℝ) 1 := by
  unfold tstar
  constructor
  · exact Real.sSup_nonneg (fun s hs => hs.1.1.le)
  · exact Real.sSup_le (fun s hs => hs.1.2.le) zero_le_one

lemma tstar_hi (hν0 : ν (Set.Iio 0) = 0) (c : ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (h : 1 - tstar ν c < u) : c ≤ quantile (cdf ν) u := by
  have hs : 1 - u < tstar ν c := by linarith
  unfold tstar at hs
  have hne : {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty] at hs
    linarith [hu.2]
  obtain ⟨s', hs', hlt⟩ := exists_lt_of_lt_csSup hne hs
  have hm : 1 - s' ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs'.1.2], by linarith [hs'.1.1]⟩
  exact le_trans hs'.2 (quantile_monotoneOn hν0 hm hu (by linarith))

lemma tstar_lo (c : ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (h : u < 1 - tstar ν c) : quantile (cdf ν) u < c := by
  by_contra hc
  push Not at hc
  have hmem : 1 - u ∈ {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)} := by
    refine ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
    simpa using hc
  have := le_csSup (⟨1, fun s hs => hs.1.2.le⟩ : BddAbove {s : ℝ | s ∈ Set.Ioo 0 1 ∧
    c ≤ quantile (cdf ν) (1 - s)}) hmem
  unfold tstar at h
  linarith

/-- `G(c) = V̄(t⋆) - t⋆ c`. -/
lemma G_eq_tstar (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (c : ℝ) :
    G ν c = Vlim ν (tstar ν c) - tstar ν c * c := by
  have ht := tstar_mem (ν := ν) c
  have := G_eq_split hν0 hν1 (a := 1 - tstar ν c) (y := c)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
    (fun u hu hlt => (tstar_lo c hu hlt).le) (fun u hu hlt => tstar_hi hν0 c hu hlt)
  rw [this, sub_sub_cancel]

lemma tstar_max (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (c : ℝ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Vlim ν t - t * c ≤ Vlim ν (tstar ν c) - tstar ν c * c := by
  intro t ht
  have := Vlim_le hν0 hν1 ht c
  rw [G_eq_tstar hν0 hν1] at this
  linarith

lemma tstar_cont (hν0 : ν (Set.Iio 0) = 0) (c : ℝ) (hcont : ContinuousAt (cdf ν) c) :
    tstar ν c = 1 - cdf ν c := by
  set S := {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)} with hS
  have hin : ∀ s ∈ Set.Ioo (0 : ℝ) 1, s < 1 - cdf ν c → s ∈ S := by
    intro s hs hlt
    refine ⟨hs, ?_⟩
    by_contra hq
    push Not at hq
    have hu : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := (quantile_le_iff hν0 hu.1 hu.2 c).1 hq.le
    linarith
  have hout : ∀ s ∈ S, s ≤ 1 - cdf ν c := by
    intro s hs
    by_contra hlt
    push Not at hlt
    have hu : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1.2], by linarith [hs.1.1]⟩
    have hlt' : 1 - s < cdf ν c := by linarith
    have hev : ∀ᶠ y in 𝓝[<] c, 1 - s < cdf ν y :=
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (eventually_gt_nhds hlt')
    obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
    have := (quantile_le_iff hν0 hu.1 hu.2 y).2 hy1.le
    have := hs.2
    have hy2 : y < c := hy2
    linarith
  unfold tstar
  rw [← hS]
  have hF1 := cdf_le_one ν c
  have hF0 := cdf_nonneg ν c
  rcases eq_or_lt_of_le (show 0 ≤ 1 - cdf ν c by linarith) with ha | ha
  · have : S = ∅ := by
      ext s; simp only [Set.mem_empty_iff_false, iff_false]
      intro hs; have := hout s hs; linarith [hs.1.1]
    rw [this, Real.sSup_empty, ← ha]
  · apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨(1 - cdf ν c) / 2, hin _ ⟨by linarith, by linarith⟩ (by linarith)⟩
    · exact hout
    · intro w hw
      refine ⟨(max w 0 + (1 - cdf ν c)) / 2, hin _ ⟨?_, ?_⟩ ?_, ?_⟩
      · have := le_max_right w 0; linarith
      · have := max_lt hw ha; linarith
      · have := max_lt hw ha; linarith
      · have := le_max_left w 0; have := max_lt hw ha; linarith

/-- The milestone `integral_pos_part_eq`. -/
lemma integral_pos_part_eq_aux (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (c : ℝ) :
    ∫ s in (0 : ℝ)..1, max (quantile (cdf ν) (1 - s) - c) 0 =
        ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) ∧
      ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) =
        Vlim ν (tstar ν c) - tstar ν c * c := by
  have ht := tstar_mem (ν := ν) c
  have h2 : ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) =
      Vlim ν (tstar ν c) - tstar ν c * c := by
    have hii : IntervalIntegrable (fun s => quantile (cdf ν) (1 - s)) volume 0 (tstar ν c) := by
      have := (quantile_intervalIntegrable' hν0 hν1 (a := 1 - tstar ν c) (b := 1)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ ⟨zero_le_one, le_rfl⟩)
      have h' := this.comp_sub_left 1
      simpa using h'.symm
    rw [intervalIntegral.integral_sub hii intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, sub_zero]
    rfl
  refine ⟨?_, h2⟩
  rw [h2, ← G_eq_tstar hν0 hν1, G_eq hν0,
    intervalIntegral.integral_comp_sub_left (fun u => max (quantile (cdf ν) u - c) 0) 1]
  simp

end Tstar
end BSPAux


open LargeBSP.Homog in
theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : Integrable id ν) (c : ℝ) (hc : 0 ≤ c) :
    ∫ s in (0 : ℝ)..1, max (quantile (cdf ν) (1 - s) - c) 0 =
        ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) ∧
      ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) =
        Vlim ν (tstar ν c) - tstar ν c * c :=
  BSPAux.integral_pos_part_eq_aux hν0 hν1 c
