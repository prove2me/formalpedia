-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.continuation_boundary_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:48.424748+00:00
-- url     : https://prove2.me/submissions/684595ca-ee7f-4d75-ba77-48f74d474235

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Theorems.Thm_OAI_SevenEighths_Supremum_continuationMargin_le_gap

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {β ω σ : ℝ} (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by
  have h := continuationMargin_le_gap β ω σ
  linarith
end OAI.SevenEighths.Supremum
