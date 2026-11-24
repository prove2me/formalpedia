-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.conv_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:30:00.705001+00:00
-- url     : https://prove2.me/submissions/f5bef3f7-f5af-4f4c-af9f-fcfa99641fac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_injective
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_conv

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
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (a b c : G → ℂ) : conv (conv a b) c = conv a (conv b c) :=
  alg_injective (by simp only [alg_conv, mul_assoc])
end GlobalTheory.BadShare.Basic
