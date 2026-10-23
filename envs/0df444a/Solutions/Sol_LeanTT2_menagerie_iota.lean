-- Prove2me | solution 1 for LeanTT2.menagerie_iota
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:36.965705+00:00
-- url     : https://prove2.me/submissions/8c1292f2-8bfd-4382-8102-96073e4b0957

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (Γ : F.Ctx) (a b e f x : F.E) :
    F.deq Γ (F.fst (F.pairT a b)) a ∧
    F.deq Γ (F.snd (F.pairT a b)) b ∧
    F.deq Γ (F.caseT a b (F.inl x)) (F.app a x) ∧
    F.deq Γ (F.caseT a b (F.inr x)) (F.app b x) ∧
    F.deq Γ (F.down (F.up x)) x ∧
    F.deq Γ (F.recW e (F.supT a f))
      (F.app (F.app (F.app e a) f) (F.recW_cont e f)) ∧
    F.deq Γ (F.recEq e a (F.reflT a)) e ∧
    F.deq Γ (F.recAcc e x (F.introAcc x f))
      (F.app (F.app (F.app e x) f) (F.recAcc_cont e f)) :=
  ⟨F.red_deq _ _ _ (F.red_fst Γ a b), F.red_deq _ _ _ (F.red_snd Γ a b),
    F.red_deq _ _ _ (F.red_case_inl Γ a b x), F.red_deq _ _ _ (F.red_case_inr Γ a b x),
    F.red_deq _ _ _ (F.red_down_up Γ x), F.red_deq _ _ _ (F.red_recW Γ e a f),
    F.red_deq _ _ _ (F.red_recEq Γ e a), F.red_deq _ _ _ (F.red_recAcc Γ e x f)⟩
