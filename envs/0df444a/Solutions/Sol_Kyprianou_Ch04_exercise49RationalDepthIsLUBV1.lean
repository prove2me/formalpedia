-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RationalDepthIsLUBV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:48:07.696548+00:00
-- url     : https://prove2.me/submissions/394a70b1-40b3-4fa7-8d39-875719d02793

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49GlobalLowerBoundRationalV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The rational depth is the actual greatest downward excursion of a bounded-below right-continuous path. -/
theorem solution
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t : NNReal, ContinuousWithinAt Y (Ici t) t)
    (hB : BddAbove (Set.range (fun t => -Y t))) :
    IsLUB (Set.range (fun t => -Y t)) (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal := by
  let E : ENNReal := ⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))
  change IsLUB (Set.range (fun t => -Y t)) E.toReal
  obtain ⟨b, hb⟩ := hB
  have hE : E ≤ ENNReal.ofReal b := by
    apply iSup_le
    intro q
    exact ENNReal.ofReal_le_ofReal (hb (Set.mem_range_self _))
  have hfin : E ≠ ⊤ := ne_of_lt (hE.trans_lt ENNReal.ofReal_lt_top)
  constructor
  · rintro x ⟨t, rfl⟩
    have hq : ∀ q : ℚ, 0 < q → -E.toReal ≤ Y (Real.toNNReal q) := by
      intro q _
      by_cases h : 0 ≤ -Y (Real.toNNReal q)
      · have hle : ENNReal.ofReal (-Y (Real.toNNReal q)) ≤ E := le_iSup (fun r : ℚ => ENNReal.ofReal (-Y (Real.toNNReal r))) q
        have hv := ENNReal.toReal_mono hfin hle
        rw [ENNReal.toReal_ofReal h] at hv
        linarith
      · linarith [ENNReal.toReal_nonneg (a := E)]
    have ht := (Kyprianou.Ch04.exercise49GlobalLowerBoundRationalV1
      Y hr (-E.toReal)).2 hq t
    linarith
  · intro x hx
    have hx0 : 0 ≤ x := by simpa [h0] using hx (Set.mem_range_self (0 : NNReal))
    have hle : E ≤ ENNReal.ofReal x := by
      apply iSup_le
      intro q
      exact ENNReal.ofReal_le_ofReal (hx (Set.mem_range_self _))
    simpa only [ENNReal.toReal_ofReal hx0] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
