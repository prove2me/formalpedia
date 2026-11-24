-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.isProj_dirac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:21.292885+00:00
-- url     : https://prove2.me/submissions/424c4521-0b83-475d-b29c-cd4565d9b3dd

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
theorem _root_.solution {G : Type} [Group G] [Fintype G] : IsProj (dirac : G → ℂ) := by
  refine ⟨?_, fun x => ?_⟩
  · ext x
    rw [conv, Finset.sum_eq_single 1]
    · simp [dirac]
    · intro y _ hy; simp [dirac, hy]
    · simp
  · by_cases h : x = 1 <;> simp [dirac, h]
end GlobalTheory.BadShare.Basic
