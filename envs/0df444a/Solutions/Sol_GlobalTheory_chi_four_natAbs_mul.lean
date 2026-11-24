-- Prove2me | solution 1 for GlobalTheory.chi_four_natAbs_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:10.301251+00:00
-- url     : https://prove2.me/submissions/5cb7c081-d7a0-41f7-9764-e385c57f963c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (D : ℤ) :
    ZMod.χ₄ (D.natAbs : ZMod 4) * D.natAbs = ZMod.χ₄ (D : ZMod 4) * D := by
  obtain ⟨m, rfl | rfl⟩ := D.eq_nat_or_neg
  · simp
  · have : ∀ a : ZMod 4, ZMod.χ₄ (-a) = -ZMod.χ₄ a := by decide
    simp [this]
end GlobalTheory
