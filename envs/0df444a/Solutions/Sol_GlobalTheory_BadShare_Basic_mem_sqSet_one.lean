-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.mem_sqSet_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:24.205655+00:00
-- url     : https://prove2.me/submissions/9dd27ec1-1a9a-482c-a8a6-171aa81b9e81

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
theorem _root_.solution {f : (ZMod g)[X]} (hf : f ∈ sqSet g 1) : f = X + C (f.coeff 0) ∧ f.coeff 0 ≠ 0 := by
  simp only [sqSet, Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨⟨c, -, rfl⟩, -, h⟩ := hf
  exact ⟨by simp, h⟩
end GlobalTheory.BadShare.Basic
