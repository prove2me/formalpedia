-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.conv_tens2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:17.598254+00:00
-- url     : https://prove2.me/submissions/2ecd4b0a-cb8e-4a7d-8f01-27a666fce4bd

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
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution {G' : Type} [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2, Fintype.sum_prod_type, Finset.sum_mul_sum, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.BadShare.Basic
