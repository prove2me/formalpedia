-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.rq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:40.290805+00:00
-- url     : https://prove2.me/submissions/67a42d50-81b4-45a8-af6d-2aff674a27cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {R : Type} [Ring R]
open GlobalTheory.IndLine.Iwasawa.Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h
namespace GlobalTheory.IndLine.Iwasawa.Grading
theorem _root_.solution : r * q = 0 := by rw [h.sum, sub_mul, sub_mul, one_mul, h.qq, h.pq, sub_zero, sub_self]
end GlobalTheory.IndLine.Iwasawa.Grading
