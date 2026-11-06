-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.canonicalMargins_weaken
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:15.863193+00:00
-- url     : https://prove2.me/submissions/86319b41-61ce-43d9-99b3-522229f3e8b5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {F M Q z c c' : ℝ}
    (h : CanonicalMargins F M Q z c) (hc : c' ≤ c) :
    CanonicalMargins F M Q z c' := by
  exact ⟨hc.trans h.1, hc.trans h.2⟩
end OAI.SevenEighths.InverseMoment
