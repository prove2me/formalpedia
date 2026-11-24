-- Prove2me | solution 1 for GlobalTheory.LaurentFinite.abs_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:08.941597+00:00
-- url     : https://prove2.me/submissions/ba889ddd-67a6-49d8-bf51-24f19605eefe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFinite
open AddMonoidAlgebra
namespace GlobalTheory.LaurentFinite
theorem _root_.solution (j n : ℤ) : |cut j n| ≤ 1 := by
  unfold cut
  split_ifs
  · rcases lt_trichotomy n 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  · simp
end GlobalTheory.LaurentFinite
