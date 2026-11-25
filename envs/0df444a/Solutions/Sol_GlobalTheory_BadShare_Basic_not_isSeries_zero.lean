-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.not_isSeries_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:20.771803+00:00
-- url     : https://prove2.me/submissions/4a2c69e9-463b-4fbc-b559-1461f772b5c3

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
theorem _root_.solution (τ : (ZMod g)[X] → GG g 0 → ℂ) : ¬ IsSeries τ := by
  rintro ⟨-, h⟩
  obtain ⟨V, -, -, ⟨L, -⟩, -⟩ := h 1 (by simp [sqSet])
  exact absurd L.hk (by omega)
end GlobalTheory.BadShare.Basic
