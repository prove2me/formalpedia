-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.continuationMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:35:32.624901+00:00
-- url     : https://prove2.me/submissions/8e46a622-fa7a-44aa-aaeb-90defdcb4d87

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {β ω σ : ℝ}
    (hω : ω < β - 7 / 8) (hσ : 0 < σ) :
    0 < continuationMargin β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ
end OAI.SevenEighths.Supremum
