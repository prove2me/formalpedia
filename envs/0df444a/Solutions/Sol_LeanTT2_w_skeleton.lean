-- Prove2me | solution 1 for LeanTT2.w_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:19.64679+00:00
-- url     : https://prove2.me/submissions/0b3d7b73-c43a-442f-8c32-5f8cfbdad429

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (Γ : F.Ctx) (A B : F.E)
    (hA : F.isType Γ A) (hB : F.ty Γ B (F.piT A F.Univ)) :
    F.isType Γ (F.wT A B) ∧
    ∀ e a f, F.deq Γ (F.recW e (F.supT a f))
      (F.app (F.app (F.app e a) f) (F.recW_cont e f)) :=
  ⟨F.ty_w Γ A B hA hB, fun e a f => F.red_deq _ _ _ (F.red_recW Γ e a f)⟩
