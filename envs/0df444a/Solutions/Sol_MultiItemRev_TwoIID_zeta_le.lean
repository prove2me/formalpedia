-- Prove2me | solution 1 for MultiItemRev.TwoIID.zeta_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:53:40.715074+00:00
-- url     : https://prove2.me/submissions/faf7ef88-991d-41b8-bd40-a07c0e13a7b5

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model
import Theorems.Thm_MultiItemRev_TwoIID_myerson_one_good

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TwoIIDZeta

/-- Easy direction of Myerson: `u · P[Y ≥ u] ≤ Rev(Y)`. -/
theorem posted_le (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (u : ℝ≥0) :
    (u : ℝ≥0∞) * ν {t | u ≤ t} ≤ MultiItemRev.Decomp.Rev1 ν := by
  rw [(MultiItemRev.TwoIID.myerson_one_good ν).1]
  exact le_iSup (fun p : ℝ≥0 => (p : ℝ≥0∞) * ν {t | p ≤ t}) u

/-- `P[Y ≥ u] ≤ r / u` for `u > 0`. -/
theorem meas_le (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) (u : ℝ) (hu : 0 < u) :
    ν {t : ℝ≥0 | u ≤ (t : ℝ)} ≤ ENNReal.ofReal ((MultiItemRev.Decomp.Rev1 ν).toReal * u⁻¹) := by
  have h := posted_le ν u.toNNReal
  have hset : {t : ℝ≥0 | u ≤ (t : ℝ)} = {t | u.toNNReal ≤ t} := by
    ext t; simp only [mem_setOf_eq]
    rw [Real.toNNReal_le_iff_le_coe]
  rw [hset]
  have hR : MultiItemRev.Decomp.Rev1 ν = ENNReal.ofReal (MultiItemRev.Decomp.Rev1 ν).toReal :=
    (ENNReal.ofReal_toReal hr).symm
  set r := (MultiItemRev.Decomp.Rev1 ν).toReal
  rw [hR] at h
  have hu' : (u.toNNReal : ℝ≥0∞) = ENNReal.ofReal u := rfl
  rw [hu'] at h
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hu]
  have hne : ENNReal.ofReal u ≠ 0 := by simpa using hu
  have hne' : ENNReal.ofReal u ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hne'), mul_comm]
  exact h


theorem lint_min_le (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) (p : ℝ≥0)
    (hrp : (MultiItemRev.Decomp.Rev1 ν).toReal ≤ p) :
    ∫⁻ y, ENNReal.ofReal ((min y p : ℝ≥0) : ℝ) ∂ν ≤
      ENNReal.ofReal (MultiItemRev.Decomp.Rev1 ν).toReal +
        ∫⁻ u in Ioc (MultiItemRev.Decomp.Rev1 ν).toReal (p : ℝ),
          ENNReal.ofReal ((MultiItemRev.Decomp.Rev1 ν).toReal * u⁻¹) := by
  set r := (MultiItemRev.Decomp.Rev1 ν).toReal with hrdef
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hmeas : Measurable (fun y : ℝ≥0 => ((min y p : ℝ≥0) : ℝ)) :=
    (measurable_id.min measurable_const).coe_nnreal_real
  rw [lintegral_eq_lintegral_meas_le ν (ae_of_all _ (fun _ => NNReal.coe_nonneg _))
    hmeas.aemeasurable]
  set B : ℝ → ℝ≥0∞ := fun u => (Ioc 0 r).indicator 1 u +
    (Ioc r p).indicator (fun u => ENNReal.ofReal (r * u⁻¹)) u with hB
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ν {a : ℝ≥0 | u ≤ ((min a p : ℝ≥0) : ℝ)} ≤ B u := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [hB]
    by_cases h1 : u ≤ r
    · rw [indicator_of_mem (show u ∈ Ioc 0 r from ⟨hu, h1⟩)]
      calc ν {a : ℝ≥0 | u ≤ ((min a p : ℝ≥0) : ℝ)} ≤ 1 := prob_le_one
        _ ≤ _ := by simp
    · push_neg at h1
      by_cases h2 : u ≤ p
      · rw [indicator_of_mem (show u ∈ Ioc r p from ⟨h1, h2⟩)]
        calc ν {a : ℝ≥0 | u ≤ ((min a p : ℝ≥0) : ℝ)} ≤ ν {t : ℝ≥0 | u ≤ (t : ℝ)} := by
              apply measure_mono
              intro a ha
              simp only [mem_setOf_eq] at ha ⊢
              exact le_trans ha (by exact_mod_cast min_le_left a p)
          _ ≤ _ := meas_le ν hr u hu
          _ ≤ _ := le_add_self
      · push_neg at h2
        have : {a : ℝ≥0 | u ≤ ((min a p : ℝ≥0) : ℝ)} = ∅ := by
          ext a
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (by exact_mod_cast min_le_right a p) h2
        rw [this, measure_empty]
        simp
  calc ∫⁻ u in Ioi 0, ν {a : ℝ≥0 | u ≤ ((min a p : ℝ≥0) : ℝ)}
      ≤ ∫⁻ u in Ioi 0, B u := setLIntegral_mono' measurableSet_Ioi hpt
    _ ≤ ∫⁻ u, B u := setLIntegral_le_lintegral _ _
    _ = (∫⁻ u, (Ioc 0 r).indicator 1 u) + ∫⁻ u,
          (Ioc r p).indicator (fun u => ENNReal.ofReal (r * u⁻¹)) u := by
        simp only [hB]
        rw [lintegral_add_left (measurable_one.indicator measurableSet_Ioc)]
    _ = _ := by
        rw [lintegral_indicator_one measurableSet_Ioc, lintegral_indicator measurableSet_Ioc,
          Real.volume_Ioc, sub_zero]

end TwoIIDZeta

theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hr : MultiItemRev.Decomp.Rev1 ν ≠ ⊤) (p : ℝ≥0) :
    let r := (MultiItemRev.Decomp.Rev1 ν).toReal
    (ν {t | p ≤ t}).toReal *
      ((∫ t, ((min t p : ℝ≥0) : ℝ) ∂ν) - r) ≤ r / Real.exp 1 := by
  intro r
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set G := (ν {t | p ≤ t}).toReal with hGdef
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hpG : (p : ℝ) * G ≤ r := by
    have h := TwoIIDZeta.posted_le ν p
    have h2 := ENNReal.toReal_mono hr h
    rw [ENNReal.toReal_mul] at h2
    simpa using h2
  have hmeas : Measurable (fun y : ℝ≥0 => ((min y p : ℝ≥0) : ℝ)) :=
    (measurable_id.min measurable_const).coe_nnreal_real
  set L := ∫⁻ y, ENNReal.ofReal ((min y p : ℝ≥0) : ℝ) ∂ν with hL
  set m := ∫ t, ((min t p : ℝ≥0) : ℝ) ∂ν with hmdef
  have hm_eq : m = L.toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => NNReal.coe_nonneg _))
      hmeas.aestronglyMeasurable
  have hLp : L ≤ ENNReal.ofReal p := by
    calc L ≤ ∫⁻ _y, ENNReal.ofReal p ∂ν := by
          apply lintegral_mono; intro y
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast min_le_right y p)
      _ = ENNReal.ofReal p := by simp
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLp
  have hm_le_p : m ≤ p := by
    rw [hm_eq]
    exact ENNReal.toReal_le_of_le_ofReal p.2 hLp
  by_cases hmr : m ≤ r
  · have : G * (m - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hG0 (by linarith)
    have : 0 ≤ r / Real.exp 1 := div_nonneg hr0 he.le
    linarith
  push_neg at hmr
  have hrp : r ≤ p := by linarith
  have hb : L ≤ ENNReal.ofReal r + ∫⁻ u in Ioc r (p : ℝ), ENNReal.ofReal (r * u⁻¹) :=
    TwoIIDZeta.lint_min_le ν hr p hrp
  rcases hr0.eq_or_lt with hr00 | hrpos
  · exfalso
    have : ∫⁻ u in Ioc r (p : ℝ), ENNReal.ofReal (r * u⁻¹) = 0 := by
      rw [← hr00]; simp
    rw [this, ← hr00, ENNReal.ofReal_zero, add_zero] at hb
    have : L = 0 := le_antisymm hb (zero_le)
    rw [hm_eq, this] at hmr
    simp at hmr
    linarith
  -- r > 0
  have hint : ∫⁻ u in Ioc r (p : ℝ), ENNReal.ofReal (r * u⁻¹) =
      ENNReal.ofReal (r * Real.log (p / r)) := by
    have hcont : ContinuousOn (fun u : ℝ => r * u⁻¹) (Icc r p) :=
      continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => (lt_of_lt_of_le hrpos hx.1).ne'))
    have hI : IntegrableOn (fun u : ℝ => r * u⁻¹) (Ioc r p) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hI]
    · congr 1
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hrp,
        integral_inv_of_pos hrpos (lt_of_lt_of_le hrpos hrp)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg hr0 (inv_nonneg.mpr (le_trans hr0 hu.1.le))
  rw [hint, ← ENNReal.ofReal_add hr0] at hb
  swap
  · apply mul_nonneg hr0
    apply Real.log_nonneg
    rw [le_div_iff₀ hrpos]; linarith
  have hm_bound : m ≤ r + r * Real.log (p / r) := by
    rw [hm_eq]
    apply ENNReal.toReal_le_of_le_ofReal _ hb
    apply add_nonneg hr0 (mul_nonneg hr0 (Real.log_nonneg _))
    rw [le_div_iff₀ hrpos]; linarith
  -- log q ≤ q / e
  set q := (p : ℝ) / r with hq
  have hqpos : 0 < q := div_pos (lt_of_lt_of_le hrpos hrp) hrpos
  have hlog : Real.log q ≤ q / Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hqpos he)
    rw [Real.log_div hqpos.ne' he.ne', Real.log_exp] at this
    linarith
  have hrq : r * q = p := by rw [hq]; field_simp
  have h1 : m - r ≤ (p : ℝ) / Real.exp 1 := by
    have : r * Real.log q ≤ r * (q / Real.exp 1) := mul_le_mul_of_nonneg_left hlog hr0
    have e2 : r * (q / Real.exp 1) = (p : ℝ) / Real.exp 1 := by rw [← hrq]; ring
    linarith
  calc G * (m - r) ≤ G * ((p : ℝ) / Real.exp 1) := mul_le_mul_of_nonneg_left h1 hG0
    _ = ((p : ℝ) * G) / Real.exp 1 := by ring
    _ ≤ r / Real.exp 1 := div_le_div_of_nonneg_right hpG he.le
