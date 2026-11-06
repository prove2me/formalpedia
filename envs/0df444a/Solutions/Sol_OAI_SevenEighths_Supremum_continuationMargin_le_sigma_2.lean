-- Prove2me | solution 2 for OAI.SevenEighths.Supremum.continuationMargin_le_sigma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:25.007077+00:00
-- url     : https://prove2.me/submissions/f3a964e1-f52e-4d33-8123-7d729ca11250

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ σ :=
  min_le_right _ _
end OAI.SevenEighths.Supremum
