-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageRationalCrossingMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:56:21.328714+00:00
-- url     : https://prove2.me/submissions/08c46dbb-1146-4d8a-9866-e21a8f65a90a

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

/-- A countable union of rationally sampled pre-hitting events is adapted. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (s : ℝ) :
    @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X u)
      {ω : Ω | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ) ∧
        s < X (Real.toNNReal (q : ℝ)) ω} := by
  have hq (q : ℚ) : @MeasurableSet Ω (naturalSigma X u)
      {ω : Ω | 0 < (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ) ∧
        s < X (Real.toNNReal (q : ℝ)) ω} := by
    by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ)
    · have hle : Real.toNNReal (q : ℝ) ≤ u :=
        Real.toNNReal_le_iff_le_coe.mpr h.2
      have hm := Kyprianou.Ch01.naturalSigma_measurable_past
        X (Real.toNNReal (q : ℝ)) u hle
      have hset : @MeasurableSet Ω (naturalSigma X u)
          {ω : Ω | s < X (Real.toNNReal (q : ℝ)) ω} :=
        hm measurableSet_Ioi
      simpa only [h.1, h.2, true_and] using hset
    · have hset :
          {ω : Ω | 0 < (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ) ∧
            s < X (Real.toNNReal (q : ℝ)) ω} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hω
        exact h ⟨hω.1, hω.2.1⟩
      rw [hset]
      exact @MeasurableSet.empty Ω (naturalSigma X u)
  simpa only [Set.setOf_exists] using
    (MeasurableSet.iUnion hq : @MeasurableSet Ω (naturalSigma X u)
      (⋃ q : ℚ, {ω : Ω | 0 < (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ) ∧
        s < X (Real.toNNReal (q : ℝ)) ω}))
