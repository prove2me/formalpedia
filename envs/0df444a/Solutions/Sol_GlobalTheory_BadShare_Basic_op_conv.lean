-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.op_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:29:57.990298+00:00
-- url     : https://prove2.me/submissions/ff03c4e7-d0de-42f6-bbbe-d6b84d4ca833

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_conv
import Theorems.Thm_GlobalTheory_BadShare_Basic_op_eq_asAlgebraHom

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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op_eq_asAlgebraHom, alg_conv, map_mul]
end GlobalTheory.BadShare.Basic
