-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.primeOK_example
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:31.798502+00:00
-- url     : https://prove2.me/submissions/efd49516-561d-46d4-8623-464f80008faf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

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
theorem _root_.solution : PrimeOK 6529 3 17 ∧ Nat.Prime 6529 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩
end GlobalTheory.BadShare.Basic
