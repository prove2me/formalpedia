-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.rationalCutoffBetweenBeforeStop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:54:56.484231+00:00
-- url     : https://prove2.me/submissions/5b98f1ca-d7d9-4a67-94e4-5a1c13fa26cd

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (t : ℝ≥0) (T : WithTop ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < T) :
    ∃ q : ℚ, 0 ≤ q ∧
      t < (q : ℝ).toNNReal ∧
      ((q : ℝ).toNNReal : WithTop ℝ≥0) < T := by
  have hToNN (q : ℚ) (htq : (t : ℝ) < (q : ℝ)) :
      0 ≤ q ∧ t < (q : ℝ).toNNReal := by
    have hpos : (0 : ℝ) ≤ (q : ℝ) :=
      le_trans t.coe_nonneg (le_of_lt htq)
    have hcoe : (((q : ℝ).toNNReal : ℝ)) = (q : ℝ) :=
      Real.coe_toNNReal _ hpos
    constructor
    · exact_mod_cast hpos
    · exact_mod_cast (show (t : ℝ) < ((q : ℝ).toNNReal : ℝ) by
        rw [hcoe]
        exact htq)
  by_cases hTop : T = ⊤
  · obtain ⟨q, hqlo, _⟩ :=
      exists_rat_btwn (show (t : ℝ) < (t : ℝ) + 1 by linarith)
    obtain ⟨hqpos, htq⟩ := hToNN q hqlo
    refine ⟨q, hqpos, htq, ?_⟩
    simpa only [hTop] using
      (WithTop.coe_lt_top ((q : ℝ).toNNReal))
  · obtain ⟨ζ, hζ⟩ := WithTop.ne_top_iff_exists.mp hTop
    subst T
    have htζ : t < ζ := WithTop.coe_lt_coe.mp ht
    obtain ⟨q, hqlo, hqhi⟩ :=
      exists_rat_btwn (show (t : ℝ) < (ζ : ℝ) by
        exact_mod_cast htζ)
    obtain ⟨hqpos, htq⟩ := hToNN q hqlo
    have hqζ : (q : ℝ).toNNReal < ζ := by
      have hpos : (0 : ℝ) ≤ (q : ℝ) :=
        le_trans t.coe_nonneg (le_of_lt hqlo)
      have hcoe : ((q : ℝ).toNNReal : ℝ) = (q : ℝ) :=
        Real.coe_toNNReal _ hpos
      exact_mod_cast (show ((q : ℝ).toNNReal : ℝ) < (ζ : ℝ) by
        rw [hcoe]
        exact hqhi)
    exact ⟨q, hqpos, htq, WithTop.coe_lt_coe.mpr hqζ⟩
