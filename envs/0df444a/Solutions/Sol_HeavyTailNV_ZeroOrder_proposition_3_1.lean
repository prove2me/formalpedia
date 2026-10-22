-- Prove2me | solution 1 for HeavyTailNV.ZeroOrder.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:11:29.701685+00:00
-- url     : https://prove2.me/submissions/a1cf7e35-cc63-4f19-8401-89c8d20565e5

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

end HTZ

theorem solution (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    twoPointLaw m1 ma α ∈ HeavyTailNV.Tail.ambiguitySet m1 ma α ∧
    ∀ q : ℝ, 0 ≤ q → q ≤ q0 m1 ma α →
      HeavyTailNV.Tail.worstCase m1 ma α q = m1 - q * (m1 ^ α / ma) ^ (1 / (α - 1)) ∧
      ∫ w, max (w - q) 0 ∂(twoPointLaw m1 ma α) = HeavyTailNV.Tail.worstCase m1 ma α q := by
  refine ⟨HTZ.tp_mem α m1 ma hα hm1 hma, fun q hq0 hq => ?_⟩
  have h := HTZ.wc_formula α m1 ma hα hm1 hma q hq0 hq
  exact ⟨h.1, h.2.trans h.1.symm⟩
