-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.markedMargins_of_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:11.685222+00:00
-- url     : https://prove2.me/submissions/02fb23b3-e540-4e15-b683-8595164b28b3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by
  refine ⟨min (m - r - 2 * z) (3 * m - 2 * r - 8 * z), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · constructor
    · have := min_le_left (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
    · have := min_le_right (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
end OAI.SevenEighths.InverseMoment
