-- Prove2me | solution 1 for HeavyTailNV.ZeroOrder.pi_properties
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:11:30.82502+00:00
-- url     : https://prove2.me/submissions/5dd5be9b-ac9e-4c8d-b2cb-35246fdd4cda

import Mathlib
import Definitions.Def_HeavyTailNV_ZeroOrder_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open HeavyTailNV.ZeroOrder HeavyTailNV.Tail

namespace HTZ

/-- basic facts about the two-point parameters -/
lemma params (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    let p := (m1 ^ α / ma) ^ (1 / (α - 1))
    let D := (ma / m1) ^ (1 / (α - 1))
    0 < p ∧ p < 1 ∧ 0 < D ∧ p * D = m1 ∧ p * D ^ α = ma := by
  intro p D
  have hα1 : 0 < α - 1 := by linarith
  have hm1a : 0 < m1 ^ α := Real.rpow_pos_of_pos hm1 α
  have hma0 : 0 < ma := lt_trans hm1a hma
  have hq1 : m1 ^ α / ma < 1 := (div_lt_one hma0).2 hma
  have hq0 : 0 < m1 ^ α / ma := div_pos hm1a hma0
  have hp0 : 0 < p := Real.rpow_pos_of_pos hq0 _
  have hp1 : p < 1 := Real.rpow_lt_one hq0.le hq1 (by positivity)
  have hD0 : 0 < D := Real.rpow_pos_of_pos (div_pos hma0 hm1) _
  have hDα1 : D ^ (α - 1) = ma / m1 := by
    simp only [D]
    rw [← Real.rpow_mul (div_pos hma0 hm1).le]
    rw [one_div, inv_mul_cancel₀ hα1.ne', Real.rpow_one]
  have hpα1 : p ^ (α - 1) = m1 ^ α / ma := by
    simp only [p]
    rw [← Real.rpow_mul hq0.le]
    rw [one_div, inv_mul_cancel₀ hα1.ne', Real.rpow_one]
  have hpD : p * D = m1 := by
    have h1 : p * D = (m1 ^ α / ma * (ma / m1)) ^ (1 / (α - 1)) := by
      simp only [p, D]
      rw [Real.mul_rpow hq0.le (div_pos hma0 hm1).le]
    have h2 : m1 ^ α / ma * (ma / m1) = m1 ^ (α - 1) := by
      rw [Real.rpow_sub_one hm1.ne']
      field_simp
    rw [h1, h2, ← Real.rpow_mul hm1.le, one_div, mul_inv_cancel₀ hα1.ne', Real.rpow_one]
  have hDα : D ^ α = D * D ^ (α - 1) := by
    rw [← Real.rpow_one_add' hD0.le (by linarith)]
    ring_nf
  have hpDα : p * D ^ α = ma := by
    rw [hDα, ← mul_assoc, hpD, hDα1]
    field_simp
  exact ⟨hp0, hp1, hD0, hpD, hpDα⟩

/-- the two-point law with mass `1 - p` at `0` and `p` at `D` -/
noncomputable def tp (p D : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ) + ENNReal.ofReal p • Measure.dirac D

lemma tp_integrable (p D : ℝ) (f : ℝ → ℝ) : Integrable f (tp p D) := by
  unfold tp
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma tp_integral (p D : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ℝ → ℝ) :
    ∫ w, f w ∂(tp p D) = (1 - p) * f 0 + p * f D := by
  unfold tp
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0]
  simp

lemma tp_prob (p D : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProbabilityMeasure (tp p D) := by
  refine ⟨?_⟩
  unfold tp
  simp only [Measure.coe_add, Pi.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hp0]
  simp

lemma tp_Iio (p D : ℝ) (hD : 0 < D) : tp p D (Set.Iio 0) = 0 := by
  unfold tp
  simp [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator, hD.not_gt]

lemma ae_nonneg {F : Measure ℝ} (h : F (Set.Iio 0) = 0) : ∀ᵐ w ∂F, 0 ≤ w := by
  rw [ae_iff]
  simpa [Set.Iio] using h

lemma int_max (F : Measure ℝ) [IsProbabilityMeasure F] (hi : Integrable (fun w : ℝ => w) F) (q : ℝ) :
    Integrable (fun w : ℝ => max (w - q) 0) F := by
  refine Integrable.mono' (hi.abs.add (integrable_const |q|)) ?_ (ae_of_all _ (fun w => ?_))
  · exact (measurable_id.sub_const q |>.max measurable_const).aestronglyMeasurable
  · simp only [Real.norm_eq_abs, Pi.add_apply]
    have h1 : 0 ≤ max (w - q) 0 := le_max_right _ _
    rw [abs_of_nonneg h1]
    rcases max_cases (w - q) 0 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; have := le_abs_self w; have := neg_abs_le q; linarith
    · rw [h]; positivity

lemma pointwise (α q D : ℝ) (hα : 1 < α) (hD : 0 < D) (hq0 : 0 ≤ q) (hq : q ≤ (α - 1) / α * D)
    (w : ℝ) (hw : 0 ≤ w) :
    max (w - q) 0 ≤ (1 - q * α / ((α - 1) * D)) * w + q / ((α - 1) * D ^ α) * w ^ α := by
  have hα1 : 0 < α - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hDα : 0 < D ^ α := Real.rpow_pos_of_pos hD α
  have hc1 : 0 ≤ 1 - q * α / ((α - 1) * D) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    have : q * α ≤ (α - 1) / α * D * α := mul_le_mul_of_nonneg_right hq hα0.le
    calc q * α ≤ (α - 1) / α * D * α := this
      _ = (α - 1) * D := by field_simp
  have hc2 : 0 ≤ q / ((α - 1) * D ^ α) := by positivity
  have hwα : 0 ≤ w ^ α := Real.rpow_nonneg hw α
  by_cases hwq : w ≤ q
  · rw [max_eq_right (by linarith)]
    positivity
  · push_neg at hwq
    rw [max_eq_left (by linarith)]
    set x := w / D with hx
    have hx0 : 0 ≤ x := by positivity
    have hwx : w = D * x := by rw [hx]; field_simp
    have hB := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ x - 1 by linarith) hα.le
    have hB' : 1 + α * (x - 1) ≤ x ^ α := by
      have : (1 + (x - 1)) = x := by ring
      rwa [this] at hB
    have hwα' : w ^ α = D ^ α * x ^ α := by
      rw [hwx, Real.mul_rpow hD.le hx0]
    have key : (1 - q * α / ((α - 1) * D)) * w + q / ((α - 1) * D ^ α) * w ^ α - (w - q)
        = q / (α - 1) * (x ^ α - α * x + (α - 1)) := by
      rw [hwα', hwx]
      field_simp
      ring
    have : 0 ≤ q / (α - 1) * (x ^ α - α * x + (α - 1)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith

section
variable (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma)
include hα hm1 hma

lemma tp_mem : tp ((m1 ^ α / ma) ^ (1 / (α - 1))) ((ma / m1) ^ (1 / (α - 1)))
    ∈ ambiguitySet m1 ma α := by
  obtain ⟨hp0, hp1, hD0, hpD, hpDα⟩ := params α m1 ma hα hm1 hma
  set p := (m1 ^ α / ma) ^ (1 / (α - 1)) with hp
  set D := (ma / m1) ^ (1 / (α - 1)) with hD
  have := tp_prob p D hp0.le hp1.le
  refine ⟨this, tp_Iio p D hD0, tp_integrable p D _, tp_integrable p D _, ?_, ?_⟩
  · rw [tp_integral p D hp0.le hp1.le (fun w => w)]
    simp [hpD]
  · rw [tp_integral p D hp0.le hp1.le (fun w => w ^ α)]
    rw [Real.zero_rpow (by linarith)]
    simp [hpDα]

lemma ub (F : Measure ℝ) (hF : F ∈ ambiguitySet m1 ma α) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ q0 m1 ma α) :
    ∫ w, max (w - q) 0 ∂F ≤ m1 - q * (m1 ^ α / ma) ^ (1 / (α - 1)) := by
  obtain ⟨hp0, hp1, hD0, hpD, hpDα⟩ := params α m1 ma hα hm1 hma
  set p := (m1 ^ α / ma) ^ (1 / (α - 1)) with hp
  set D := (ma / m1) ^ (1 / (α - 1)) with hD
  obtain ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ := hF
  have := hprob
  have hα1 : 0 < α - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hq' : q ≤ (α - 1) / α * D := hq
  have hg : Integrable (fun w : ℝ => (1 - q * α / ((α - 1) * D)) * w
      + q / ((α - 1) * D ^ α) * w ^ α) F :=
    (hi1.const_mul _).add (hiα.const_mul _)
  have h1 : ∫ w, max (w - q) 0 ∂F ≤ ∫ w, ((1 - q * α / ((α - 1) * D)) * w
      + q / ((α - 1) * D ^ α) * w ^ α) ∂F := by
    refine integral_mono_ae (int_max F hi1 q) hg ?_
    filter_upwards [ae_nonneg hneg] with w hw
    exact pointwise α q D hα hD0 hq0 hq' w hw
  refine h1.trans (le_of_eq ?_)
  rw [integral_add (hi1.const_mul _) (hiα.const_mul _), integral_const_mul, integral_const_mul,
    hmean, hmom]
  rw [← hpD, ← hpDα]
  have hDα : 0 < D ^ α := Real.rpow_pos_of_pos hD0 α
  field_simp
  ring

lemma wc_formula (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ q0 m1 ma α) :
    worstCase m1 ma α q = m1 - q * (m1 ^ α / ma) ^ (1 / (α - 1)) ∧
    ∫ w, max (w - q) 0 ∂(twoPointLaw m1 ma α) = m1 - q * (m1 ^ α / ma) ^ (1 / (α - 1)) := by
  obtain ⟨hp0, hp1, hD0, hpD, hpDα⟩ := params α m1 ma hα hm1 hma
  set p := (m1 ^ α / ma) ^ (1 / (α - 1)) with hp
  set D := (ma / m1) ^ (1 / (α - 1)) with hD
  have hα1 : 0 < α - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hqD : q ≤ D := by
    have : (α - 1) / α * D ≤ D := by
      have : (α - 1) / α ≤ 1 := by rw [div_le_one hα0]; linarith
      nlinarith
    exact hq.trans this
  have hval : ∫ w, max (w - q) 0 ∂(twoPointLaw m1 ma α) = m1 - q * p := by
    have : twoPointLaw m1 ma α = tp p D := rfl
    rw [this, tp_integral p D hp0.le hp1.le (fun w => max (w - q) 0)]
    rw [max_eq_right (by linarith : (0 : ℝ) - q ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ D - q)]
    nlinarith
  refine ⟨?_, hval⟩
  unfold worstCase
  apply IsGreatest.csSup_eq
  refine ⟨⟨twoPointLaw m1 ma α, tp_mem α m1 ma hα hm1 hma, hval⟩, ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact ub α m1 ma hα hm1 hma F hF q hq0 hq

end

section
variable (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma)
include hα hm1 hma

lemma bdd_img (q : ℝ) :
    BddAbove ((fun F : Measure ℝ => ∫ w, max (w - q) 0 ∂F) '' ambiguitySet m1 ma α) := by
  refine ⟨m1 + |q|, ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ := hF
  have := hprob
  have h1 : ∫ w, max (w - q) 0 ∂F ≤ ∫ w, (w + |q|) ∂F := by
    refine integral_mono_ae (int_max F hi1 q) (hi1.add (integrable_const _)) ?_
    filter_upwards [ae_nonneg hneg] with w hw
    refine max_le ?_ (by positivity)
    have := neg_le_abs q
    linarith
  refine h1.trans (le_of_eq ?_)
  rw [integral_add hi1 (integrable_const _), hmean]
  simp

lemma nonempty_img (q : ℝ) :
    ((fun F : Measure ℝ => ∫ w, max (w - q) 0 ∂F) '' ambiguitySet m1 ma α).Nonempty :=
  ⟨_, ⟨_, tp_mem α m1 ma hα hm1 hma, rfl⟩⟩

lemma le_wc (F : Measure ℝ) (hF : F ∈ ambiguitySet m1 ma α) (q : ℝ) :
    ∫ w, max (w - q) 0 ∂F ≤ worstCase m1 ma α q :=
  le_csSup (bdd_img α m1 ma hα hm1 hma q) ⟨F, hF, rfl⟩

lemma wc_le (q c : ℝ) (h : ∀ F ∈ ambiguitySet m1 ma α, ∫ w, max (w - q) 0 ∂F ≤ c) :
    worstCase m1 ma α q ≤ c := by
  unfold worstCase
  refine csSup_le (nonempty_img α m1 ma hα hm1 hma q) ?_
  rintro _ ⟨F, hF, rfl⟩
  exact h F hF

lemma wc_anti : Antitone (worstCase m1 ma α) := by
  intro q q' hqq'
  refine wc_le α m1 ma hα hm1 hma q' _ (fun F hF => ?_)
  obtain ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ := hF
  have := hprob
  refine le_trans ?_ (le_wc α m1 ma hα hm1 hma F ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ q)
  exact integral_mono (int_max F hi1 q') (int_max F hi1 q)
    (fun w => max_le_max (sub_le_sub_left hqq' w) le_rfl)

lemma wc_convex : ConvexOn ℝ Set.univ (worstCase m1 ma α) := by
  refine ⟨convex_univ, fun q1 _ q2 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine wc_le α m1 ma hα hm1 hma _ _ (fun F hF => ?_)
  obtain ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ := hF
  have := hprob
  have hF' : F ∈ ambiguitySet m1 ma α := ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩
  have h1 : ∫ w, max (w - (a * q1 + b * q2)) 0 ∂F ≤
      ∫ w, (a * max (w - q1) 0 + b * max (w - q2) 0) ∂F := by
    refine integral_mono (int_max F hi1 _) (((int_max F hi1 q1).const_mul a).add
      ((int_max F hi1 q2).const_mul b)) (fun w => ?_)
    have e1 := le_max_left (w - q1) 0
    have e2 := le_max_left (w - q2) 0
    have e3 := le_max_right (w - q1) 0
    have e4 := le_max_right (w - q2) 0
    refine max_le ?_ (by positivity)
    have h5 : a * w + b * w = w := by rw [← add_mul, hab, one_mul]
    have h6 := mul_le_mul_of_nonneg_left e1 ha
    have h7 := mul_le_mul_of_nonneg_left e2 hb
    nlinarith
  refine h1.trans ?_
  rw [integral_add ((int_max F hi1 q1).const_mul a) ((int_max F hi1 q2).const_mul b),
    integral_const_mul, integral_const_mul]
  have h2 := le_wc α m1 ma hα hm1 hma F hF' q1
  have h3 := le_wc α m1 ma hα hm1 hma F hF' q2
  nlinarith

lemma wc_nonpos (q : ℝ) (hq : q ≤ 0) : worstCase m1 ma α q + q = m1 := by
  have hval : ∀ F ∈ ambiguitySet m1 ma α, ∫ w, max (w - q) 0 ∂F = m1 - q := by
    intro F hF
    obtain ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ := hF
    have := hprob
    have : ∫ w, max (w - q) 0 ∂F = ∫ w, (w - q) ∂F := by
      refine integral_congr_ae ?_
      filter_upwards [ae_nonneg hneg] with w hw
      exact max_eq_left (by linarith)
    rw [this, integral_sub hi1 (integrable_const q), hmean]
    simp
  have h1 : worstCase m1 ma α q ≤ m1 - q := wc_le α m1 ma hα hm1 hma q _ (fun F hF => (hval F hF).le)
  have h2 : m1 - q ≤ worstCase m1 ma α q := by
    have := le_wc α m1 ma hα hm1 hma _ (tp_mem α m1 ma hα hm1 hma) q
    rwa [hval _ (tp_mem α m1 ma hα hm1 hma)] at this
  linarith

lemma wc_nonneg (q : ℝ) : 0 ≤ worstCase m1 ma α q := by
  have h := le_wc α m1 ma hα hm1 hma _ (tp_mem α m1 ma hα hm1 hma) q
  refine le_trans ?_ h
  exact integral_nonneg (fun w => le_max_right _ _)

lemma wc_tendsto : Tendsto (worstCase m1 ma α) atTop (𝓝 0) := by
  have hα1 : 0 < α - 1 := by linarith
  have hlim : Tendsto (fun q : ℝ => ma / q ^ (α - 1)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_rpow_atTop hα1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun q => wc_nonneg α m1 ma hα hm1 hma q)) ?_
  filter_upwards [eventually_gt_atTop 0] with q hq
  refine wc_le α m1 ma hα hm1 hma q _ (fun F hF => ?_)
  obtain ⟨hprob, hneg, hi1, hiα, hmean, hmom⟩ := hF
  have := hprob
  have hqα : 0 < q ^ (α - 1) := Real.rpow_pos_of_pos hq _
  have h1 : ∫ w, max (w - q) 0 ∂F ≤ ∫ w, (w ^ α / q ^ (α - 1)) ∂F := by
    refine integral_mono_ae (int_max F hi1 q) (hiα.div_const _) ?_
    filter_upwards [ae_nonneg hneg] with w hw
    by_cases hwq : w ≤ q
    · rw [max_eq_right (by linarith)]
      positivity
    · push_neg at hwq
      rw [max_eq_left (by linarith)]
      have hw0 : 0 < w := by linarith
      have h2 : q ^ (α - 1) ≤ w ^ (α - 1) := Real.rpow_le_rpow hq.le hwq.le (by linarith)
      have h3 : w ^ α = w * w ^ (α - 1) := by
        rw [← Real.rpow_one_add' hw0.le (by linarith)]
        ring_nf
      rw [le_div_iff₀ hqα, h3]
      nlinarith
  refine h1.trans (le_of_eq ?_)
  rw [integral_div, hmom]

end

end HTZ

theorem solution (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    Antitone (HeavyTailNV.Tail.worstCase m1 ma α) ∧
    ConvexOn ℝ Set.univ (HeavyTailNV.Tail.worstCase m1 ma α) ∧
    (∀ q : ℝ, q ≤ 0 → HeavyTailNV.Tail.worstCase m1 ma α q + q = m1) ∧
    Tendsto (HeavyTailNV.Tail.worstCase m1 ma α) atTop (𝓝 0) :=
  ⟨HTZ.wc_anti α m1 ma hα hm1 hma, HTZ.wc_convex α m1 ma hα hm1 hma,
    fun q hq => HTZ.wc_nonpos α m1 ma hα hm1 hma q hq, HTZ.wc_tendsto α m1 ma hα hm1 hma⟩
