-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.isProj_tens2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:14.683824+00:00
-- url     : https://prove2.me/submissions/02013c08-01f0-4cfc-a8eb-161ac55fca11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_conv_tens2

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
theorem _root_.solution {G' : Type} [Group G'] [Fintype G'] {a : G → ℂ} {b : G' → ℂ} (ha : IsProj a) (hb : IsProj b) :
    IsProj (tens2 a b) := by
  refine ⟨by rw [conv_tens2, ha.1, hb.1], fun x => ?_⟩
  simp only [tens2, Prod.fst_inv, Prod.snd_inv, map_mul, ha.2, hb.2]
end GlobalTheory.BadShare.Basic
