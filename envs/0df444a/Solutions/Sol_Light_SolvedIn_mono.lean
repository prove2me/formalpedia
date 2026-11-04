-- Prove2me | solution 1 for Light.SolvedIn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:14.622676+00:00
-- url     : https://prove2.me/submissions/fd006f8b-16c6-4c91-af8a-b1b4c9357a89

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks

set_option autoImplicit false
section
open Light
open ThreeSumApsp
namespace Light
namespace SolvedIn
theorem _root_.solution {task : Task} {T T' : ℕ → ℝ → ℝ} (h : SolvedIn task T)
    (hT : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ u → T n u ≤ T' n u) : SolvedIn task T' := by
  obtain ⟨P, p, Tn, need, h1, h2, h3⟩ := h
  refine ⟨P, p, Tn, need, h1, h2, fun n U u hn hU hu => (h3 n U u hn hU hu).trans (hT n u hn ?_)⟩
  exact le_trans (by exact_mod_cast hU) hu
end SolvedIn
end Light
