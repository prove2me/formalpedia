-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.isUp_transv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:23.264298+00:00
-- url     : https://prove2.me/submissions/1329431b-1c0f-4126-bccd-93d6430b1474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_transv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (a b : Fin N) (h : a < b) : IsUp g N (transv a b h.ne) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [transv_apply, if_pos rfl, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ h
  · rw [transv_apply, if_neg hij.ne', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h hij
end GlobalTheory.BadShare.Basic
