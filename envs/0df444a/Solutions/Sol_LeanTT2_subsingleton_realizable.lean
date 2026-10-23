-- Prove2me | solution 1 for LeanTT2.subsingleton_realizable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:27.861395+00:00
-- url     : https://prove2.me/submissions/bbcf2c2a-7712-4ae8-98ce-233fb011c589

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (Γ : F.Ctx) (A B : F.E)
    (hA : F.isType Γ A) (hB : F.ty Γ B (F.piT A F.Univ)) :
    F.isType Γ (F.truncT (F.wT A B)) ∧
    F.isProp Γ (F.truncT (F.wT A B)) := by
  have h := F.ty_trunc Γ _ (F.ty_w Γ A B hA hB)
  exact ⟨F.isType_of_isProp Γ _ h, h⟩
