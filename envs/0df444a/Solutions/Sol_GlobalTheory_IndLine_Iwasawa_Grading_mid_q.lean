-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.mid_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:50.933854+00:00
-- url     : https://prove2.me/submissions/df3809ff-46ac-49aa-8667-ea96148c383b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_qr
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_rq

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
theorem _root_.solution (Z : R) : mid p r q Z * q = q * mid p r q Z := by
  simp only [mid, add_mul, mul_add, mul_assoc, h.qq, h.rq, h.pq, mul_zero, zero_add]
  simp only [← mul_assoc, h.qq, h.qr, h.qp, zero_mul, zero_add]
end GlobalTheory.IndLine.Iwasawa.Grading
