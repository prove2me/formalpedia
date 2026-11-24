-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.standard_edge_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:09.457797+00:00
-- url     : https://prove2.me/submissions/ba32dacb-f5b0-43df-9599-35173c538247

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
theorem _root_.solution (a b : Fin 5) : (levStandard g 5 true 1 2 (by norm_num)).Edge a b ↔
    (a, b) = (0, 3) ∨ (a, b) = (1, 2) ∨ (a, b) = (3, 4) := by
  simp only [Lev.Edge, levStandard, levOfChar, if_true]
  revert a b; decide
end GlobalTheory.BadShare.Basic
