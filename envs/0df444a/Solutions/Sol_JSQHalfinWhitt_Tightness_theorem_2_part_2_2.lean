-- Prove2me | solution 1 for JSQHalfinWhitt.Tightness.theorem_2_part_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:28:42.900886+00:00
-- url     : https://prove2.me/submissions/e3424064-f27e-4673-aa09-233cdddb5954

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Theorems.Thm_JSQHalfinWhitt_Tightness_theorem_2

open JSQHalfinWhitt.Tightness in
theorem solution (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → β < Real.sqrt n →
      ∀ π : State n → ℝ, IsStationaryDist (genQ n (lamHW β n)) π →
        expect π (fun q => |Real.sqrt n * (((q.1 0 : ℝ) - n) / n)|) ≤ C ∧
          expect π (fun q => |Real.sqrt n * ((q.1 1 : ℝ) / n)|) ≤ C := by
  obtain ⟨C, hC⟩ := JSQHalfinWhitt.Tightness.theorem_2 β hβ
  exact ⟨C, fun n hn hβn π hπ => (hC n hn hβn π hπ).1⟩
