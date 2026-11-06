-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.exists_gt_supremum_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:42.539073+00:00
-- url     : https://prove2.me/submissions/5b4e9056-9e48-4a76-b806-b501a9cd41fe

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  apply (lt_csSup_iff hbounded hne).mp
  linarith
end OAI.SevenEighths.Supremum
