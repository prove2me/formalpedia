-- Prove2me | solution 2 for OAI.SevenEighths.Supremum.continuationMargin_le_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:11.917205+00:00
-- url     : https://prove2.me/submissions/27e6e78c-4f84-4088-81b1-47171d73700c

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω :=
  min_le_left _ _
end OAI.SevenEighths.Supremum
