-- Prove2me | solution 1 for LeanTT2.deq_undecidable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:52.258384+00:00
-- url     : https://prove2.me/submissions/5c5848b9-0370-497e-95f5-c9d996e60a9e

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (C : Counter F)
    (dec : F.Ctx → F.E → F.E → Bool)
    (hdec1 : ∀ (Γ : F.Ctx) (a b : F.E), F.deq Γ a b → dec Γ a b = true)
    (hdec2 : ∀ (Γ : F.Ctx) (a b : F.E), dec Γ a b = true → F.deq Γ a b) :
    False := by
  refine C.hundec (dec C.Γ (F.app (F.app C.f (C.num 0)) C.acc0) C.unit) ⟨fun hd => ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    exact C.no_unit (fun k => by simpa using hc k) (hdec2 _ _ _ hd)
  · rintro ⟨k, hk⟩
    obtain ⟨h, hty, hdeq⟩ := C.chain k
    exact hdec1 _ _ _ (F.deq_trans _ _ _ _ hdeq (C.step_false k h hty hk))
