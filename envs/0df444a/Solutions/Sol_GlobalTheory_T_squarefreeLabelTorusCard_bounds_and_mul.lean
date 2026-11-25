-- Prove2me | solution 1 for GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:10.515454+00:00
-- url     : https://prove2.me/submissions/82f9dcdb-266d-40a2-af04-c09ed2791ac7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMulStatement
import Theorems.Thm_GlobalTheory_BadShare_torusCard_bounds_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  first | exact @GlobalTheory.BadShare.torusCard_bounds_mul | exact GlobalTheory.BadShare.torusCard_bounds_mul | (intros; apply GlobalTheory.BadShare.torusCard_bounds_mul <;> assumption)
end _root_.GlobalTheory.T
