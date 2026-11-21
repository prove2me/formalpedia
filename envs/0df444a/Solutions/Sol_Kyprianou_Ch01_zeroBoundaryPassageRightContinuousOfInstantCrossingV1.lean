-- Prove2me | solution 1 for Kyprianou.Ch01.zeroBoundaryPassageRightContinuousOfInstantCrossingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:46:38.095607+00:00
-- url     : https://prove2.me/submissions/49e4dbb2-c4f6-4570-b679-283e281f6d46

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageEventuallyLtOfInstantCrossingV2
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hCross : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω) :
    ContinuousWithinAt
      (fun u : ℝ≥0 =>
        if u = 0 then (0 : ℝ)
        else (match firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some v => (v : ℝ))) (Ici (0 : ℝ≥0)) 0 := by
  unfold ContinuousWithinAt
  simp only [if_pos rfl]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u = 0
    · simpa [hu] using ha
    · cases hPass : firstUpperPassage X (u : ℝ) ω with
      | top => simpa [hu, hPass] using ha
      | coe w =>
          have hw0 : (0 : ℝ) ≤ (w : ℝ) := by
            exact_mod_cast (show (0 : ℝ≥0) ≤ w from zero_le)
          exact lt_of_lt_of_le ha (by simpa [hu, hPass] using hw0)
  · intro a ha
    exact zeroBoundaryPassageEventuallyLtOfInstantCrossingV2
      X ω hCross a ha
