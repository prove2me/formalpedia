-- Prove2me | solution 1 for GlobalTheory.BadShare.degType_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:44.577495+00:00
-- url     : https://prove2.me/submissions/e15732bd-ab8a-4373-adf3-52e56b2288a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : ∀ d ∈ degType g f, 0 < d := by
  intro d hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hd
  exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).natDegree_pos
end GlobalTheory.BadShare
