-- Prove2me | solution 1 for Light.timeUpTo_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:55.188203+00:00
-- url     : https://prove2.me/submissions/89986413-38cf-4bdb-ae8c-0b13be8b8069

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks

set_option autoImplicit false
section
open Light
open ThreeSumApsp
namespace Light
theorem _root_.solution {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · exact (Nat.floor_le hu).trans (le_max_left u 0)
  · rw [Nat.floor_of_nonpos hu, Nat.cast_zero]
    exact le_max_right u 0
end Light
