-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41EventClockStopV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:42.80341+00:00
-- url     : https://prove2.me/submissions/32ce62cc-4b89-45cf-b516-0ff72399d7d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (F : Filtration NNReal inferInstance)
    (t : NNReal) (A : Set Ω) (hA : MeasurableSet[F t] A) :
    IsStoppingTime F (fun w => if w ∈ A then (t : WithTop NNReal) else ⊤) := by
  classical
  intro s
  by_cases hs : t ≤ s
  · have he : {w | (if w ∈ A then (t : WithTop NNReal) else ⊤) ≤ (s : WithTop NNReal)} = A := by
      ext w
      change (if w ∈ A then (t : WithTop NNReal) else ⊤) ≤ (s : WithTop NNReal) ↔ w ∈ A
      by_cases hw : w ∈ A
      · simp only [if_pos hw, hw, iff_true]
        exact WithTop.coe_le_coe.mpr hs
      · simp only [if_neg hw, hw, iff_false]
        exact not_le_of_gt (WithTop.coe_lt_top s)
    rw [he]
    exact (F.mono hs) _ hA
  · have he : {w | (if w ∈ A then (t : WithTop NNReal) else ⊤) ≤ (s : WithTop NNReal)} = ∅ := by
      ext w
      change (if w ∈ A then (t : WithTop NNReal) else ⊤) ≤ (s : WithTop NNReal) ↔ False
      by_cases hw : w ∈ A
      · rw [if_pos hw, iff_false]
        exact fun h => hs (WithTop.coe_le_coe.mp h)
      · rw [if_neg hw, iff_false]
        exact not_le_of_gt (WithTop.coe_lt_top s)
    rw [he]
    exact @MeasurableSet.empty Ω (F s)
