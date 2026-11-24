-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLevyTruncatedMomentFromLocalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:22:48.654082+00:00
-- url     : https://prove2.me/submissions/be8249bf-5777-4b4d-825b-a3c711c42a87

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (r : ℝ) (hr : 0 < r)
    (hsmall : Integrable (fun x : ℝ => x) (ν.restrict (Set.Ioo 0 r))) :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) (ν.restrict (Set.Ioi 0)) := by
  have hsub : Set.Ici r ⊆ {x : ℝ | r ≤ |x|} :=
    fun x hx => hx.trans (le_abs_self x)
  have hfin : ν (Set.Ici r) < ⊤ :=
    (measure_mono hsub).trans_lt (hν.measure_setOf_abs_ge_lt_top hr)
  letI : IsFiniteMeasure (ν.restrict (Set.Ici r)) := isFiniteMeasure_restrict.mpr hfin.ne
  have hc : Continuous (fun x : ℝ => min (1 : ℝ) |x|) := continuous_const.min continuous_abs
  have hI : IntegrableOn (fun x : ℝ => min (1 : ℝ) |x|) (Set.Ioo 0 r) ν := by
    refine hsmall.mono' hc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := ν) measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg x)), abs_of_nonneg hx.1.le]
    exact min_le_right _ _
  have hJ : IntegrableOn (fun x : ℝ => min (1 : ℝ) |x|) (Set.Ici r) ν := by
    refine (integrable_const (1:ℝ) (μ := ν.restrict (Set.Ici r))).mono' hc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg x))]
      exact min_le_left _ _
  have he : Set.Ioo (0:ℝ) r ∪ Set.Ici r = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact hr.trans_le h
    · intro hx
      by_cases h : x < r
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr (le_of_not_gt h)
  change IntegrableOn _ (Set.Ioi 0) ν
  rw [← he]
  exact integrableOn_union.mpr ⟨hI,hJ⟩
