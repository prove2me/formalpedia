-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T19:05:02.507567+00:00
-- url     : https://prove2.me/submissions/a044bba2-485b-45fc-ad34-5b0590cddeb7

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Definitions.Def_weakCompositionFiber
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weakCompositionFiber_card_eq_sym

open scoped BigOperators

theorem solution
    (A : Type*) [Fintype A] [DecidableEq A] (k : Nat) :
    Fintype.card (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber A k) =
      Nat.choose (k + Fintype.card A - 1) k := by
  calc
    Fintype.card (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber A k) =
        Fintype.card (Sym A k) :=
      OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_eq_sym A k
    _ = Nat.choose (Fintype.card A + k - 1) k :=
      Sym.card_sym_eq_choose k
    _ = Nat.choose (k + Fintype.card A - 1) k := by
      congr 1 <;> omega