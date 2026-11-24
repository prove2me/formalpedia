-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.conv_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:16.693125+00:00
-- url     : https://prove2.me/submissions/a3129331-029e-4edf-8f2a-92c65d819c13

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
theorem _root_.solution {ι : Type} [Fintype ι] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens, Finset.prod_univ_sum, Fintype.piFinset_univ, ← Finset.prod_mul_distrib, Pi.mul_apply, Pi.inv_apply]
end GlobalTheory.BadShare.Basic
