-- Prove2me | solution 2 for OAI.SevenEighths.Supremum.exists_gt_supremum_sub
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:43.687261+00:00
-- url     : https://prove2.me/submissions/0bb6283c-9b03-499d-92b8-7dad3157e699

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section

theorem solution {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x :=
  exists_lt_of_lt_csSup hne (by linarith)
