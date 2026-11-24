-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.isNilpotent_of_isUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:19.830935+00:00
-- url     : https://prove2.me/submissions/5c9996a0-38e6-4664-8572-8fec9eacb947

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
theorem _root_.solution {u : GG g N} (hu : IsUp g N u) : IsNilpotent (u.val - 1) := by
  have ht : (u.val - 1).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp [hu.2 a b h', h'.ne']
  have hc := Matrix.charpoly_of_upperTriangular _ ht
  have h0 := Matrix.aeval_self_charpoly (u.val - 1)
  rw [hc] at h0
  refine ⟨N, ?_⟩
  simpa [hu.1] using h0
end GlobalTheory.BadShare.Basic
