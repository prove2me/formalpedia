-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.markedMargins_subcollection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:12.385611+00:00
-- url     : https://prove2.me/submissions/e8ca7767-c257-444e-8af9-79932d781bc5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {m r z z' c : ℝ}
    (h : MarkedMargins m r z c) (hz : z' ≤ z) :
    MarkedMargins m r z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith
end OAI.SevenEighths.InverseMoment
