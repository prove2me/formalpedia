-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLevySmallMomentExtendsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:16:26.399781+00:00
-- url     : https://prove2.me/submissions/0488dc58-4540-4f01-bc59-7753d0607df1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hi : Integrable (fun x : ℝ => x) (ν.restrict (Ioo (0 : ℝ) r))) :
    Integrable (fun x : ℝ => min 1 |x|) (ν.restrict (Ioi (0 : ℝ))) := by
  let g : ℝ → ℝ := fun x => min 1 |x|
  have hsmall : IntegrableOn g (Ioo (0 : ℝ) r) ν := by
    apply hi.congr
    filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Ioo] with x hx
    simp [g, abs_of_pos hx.1, min_eq_right (hx.2.le.trans hr1)]
  have htfin : ν (Ici r) < ⊤ :=
    (measure_mono (show Ici r ⊆ {x : ℝ | r ≤ |x|} from
      fun x hx => hx.trans (le_abs_self x))).trans_lt (hν.measure_setOf_abs_ge_lt_top hr)
  letI : IsFiniteMeasure (ν.restrict (Ici r)) := isFiniteMeasure_restrict.mpr htfin.ne
  have htail : IntegrableOn g (Ici r) ν := by
    apply (integrable_const (1 : ℝ) (μ := ν.restrict (Ici r))).mono'
      (by unfold g; fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg x))]
    exact min_le_left _ _
  have he : Ioo (0 : ℝ) r ∪ Ici r = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hr.trans_le h
    · intro h
      by_cases hx : x < r
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (le_of_not_gt hx)
  change IntegrableOn g (Ioi 0) ν
  rw [← he]
  exact hsmall.union htail
