-- Prove2me | solution 1 for MultiItemRev.KSeparate.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:32:28.490014+00:00
-- url     : https://prove2.me/submissions/cfb40f2d-9893-4511-aa33-164085d7e4a1

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KSeparate_myerson_one_good

open MeasureTheory
open scoped NNReal ENNReal

namespace KSepLem20Aux
open MultiItemRev.KSeparate

/-- `∫_{[a,∞)} x⁻² dx = 1/a` for `a ≥ 1`. -/
lemma lintegral_inv_sq (a : ℝ) (ha : 0 < a) :
    ∫⁻ x in Set.Ici a, ENNReal.ofReal (1 / x ^ 2) = ENNReal.ofReal (1 / a) := by
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  have hcongr : Set.EqOn (fun x : ℝ => ENNReal.ofReal (1 / x ^ 2))
      (fun x => ENNReal.ofReal (x ^ (-2 : ℝ))) (Set.Ioi a) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha hx
    simp only
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        Real.rpow_nonneg (lt_trans ha hx).le _),
    integral_Ioi_rpow_of_lt (by norm_num) ha]
  congr 1
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- The equal-revenue tail: `P[V ≥ q] = 1 / max q 1` for `q > 0`. -/
lemma erLaw_tail (q : ℝ≥0) (hq : 0 < q) :
    erLaw {t | q ≤ t} = ENNReal.ofReal (1 / max (q : ℝ) 1) := by
  unfold erLaw
  rw [Measure.map_apply measurable_real_toNNReal (measurableSet_le measurable_const measurable_id : MeasurableSet {t : ℝ≥0 | q ≤ t})]
  have hset : Real.toNNReal ⁻¹' {t | q ≤ t} = Set.Ici (q : ℝ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · intro h
      by_contra hx
      push Not at hx
      have : x.toNNReal ≤ q.toReal.toNNReal := Real.toNNReal_le_toNNReal hx.le
      simp at this
      by_cases hx0 : x ≤ 0
      · rw [Real.toNNReal_of_nonpos hx0] at h
        exact absurd h (not_le.mpr hq)
      · push Not at hx0
        have := (Real.le_toNNReal_iff_coe_le hx0.le).mp h
        linarith
    · intro h
      exact (Real.le_toNNReal_iff_coe_le (le_trans q.2 h)).mpr h
  rw [hset, withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.Ici_inter_Ici, lintegral_inv_sq _ (lt_of_lt_of_le one_pos (le_max_right _ _))]

lemma erLaw_univ : erLaw Set.univ = 1 := by
  unfold erLaw
  rw [Measure.map_apply measurable_real_toNNReal MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_inv_sq 1 one_pos]
  simp

lemma tail_map (r p : ℝ≥0) :
    (erLaw.map (fun t => r * t)) {t | p ≤ t} = erLaw {t | p ≤ r * t} := by
  rw [Measure.map_apply (by fun_prop)
    (measurableSet_le measurable_const measurable_id : MeasurableSet {t : ℝ≥0 | p ≤ t})]
  rfl

/-- Real-number core of the equivalence. -/
lemma core (p r a : ℝ) (hp : 0 < p) (hr : 0 < r) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a ≤ 1 / max (p / r) 1 ↔ p * a ≤ r := by
  rw [le_div_iff₀ (lt_of_lt_of_le one_pos (le_max_right _ _))]
  constructor
  · intro h
    have := le_trans (mul_le_mul_of_nonneg_left (le_max_left (p / r) 1) ha) h
    rw [mul_div_assoc', div_le_one hr] at this
    linarith
  · intro h
    rcases le_total (p / r) 1 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1, mul_div_assoc', div_le_one hr]; linarith

end KSepLem20Aux

open KSepLem20Aux MultiItemRev.KSeparate in
theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    MultiItemRev.Decomp.Rev1 ν ≤ (r : ℝ≥0∞) ↔
      StochDominated ν (erLaw.map (fun t => r * t)) := by
  rw [(myerson_one_good ν).1, iSup_le_iff]
  unfold StochDominated
  simp only [tail_map]
  refine forall_congr' fun p => ?_
  rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0) ≤ p) with hp | hp
  · subst hp
    have : {t : ℝ≥0 | 0 ≤ r * t} = Set.univ := by ext; simp
    rw [this, erLaw_univ]
    simp [prob_le_one]
  rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0) ≤ r) with hr | hr
  · subst hr
    have : {t : ℝ≥0 | p ≤ 0 * t} = ∅ := by
      ext t; simp [hp.ne']
    rw [this, measure_empty]
    simp [hp.ne']
  have hset : {t : ℝ≥0 | p ≤ r * t} = {t | p / r ≤ t} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [div_le_iff₀ hr, mul_comm]
  rw [hset, erLaw_tail _ (div_pos hp hr)]
  set a := (ν {t | p ≤ t}).toReal with ha
  have hfin : ν {t | p ≤ t} ≠ ⊤ := measure_ne_top _ _
  have ha' : ν {t | p ≤ t} = ENNReal.ofReal a := (ENNReal.ofReal_toReal hfin).symm
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  rw [ha', ← ENNReal.ofReal_coe_nnreal (p := p), ← ENNReal.ofReal_coe_nnreal (p := r),
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity),
    NNReal.coe_div]
  exact (core p r a hp hr ha0 ha1).symm
