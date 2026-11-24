-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.up_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:13.542287+00:00
-- url     : https://prove2.me/submissions/8764f2b4-ba6a-4a39-a8b7-bde48faf8416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_qr
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_rr

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
theorem _root_.solution (Z : R) : up p r q Z * r = p * Z * r := by
  simp only [up, add_mul, mul_assoc, h.rr, h.qr, mul_zero, add_zero]
end GlobalTheory.IndLine.Iwasawa.Grading
