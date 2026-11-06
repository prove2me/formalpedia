-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.canonicalMargins_subcollection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:13.205393+00:00
-- url     : https://prove2.me/submissions/c41b9d63-d660-47d7-be83-6b997ddd963d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {F M Q z z' c : ℝ}
    (h : CanonicalMargins F M Q z c) (hz : z' ≤ z) :
    CanonicalMargins F M Q z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith
end OAI.SevenEighths.InverseMoment
