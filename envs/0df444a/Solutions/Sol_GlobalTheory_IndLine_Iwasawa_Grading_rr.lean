-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.rr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:41.036403+00:00
-- url     : https://prove2.me/submissions/1338a9c4-0f60-4c38-bb41-5603123f090f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_pr
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_qr

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
theorem _root_.solution : r * r = r := by
  conv_lhs => enter [1]; rw [h.sum]
  rw [sub_mul, sub_mul, one_mul, h.pr, h.qr, sub_zero, sub_zero]
end GlobalTheory.IndLine.Iwasawa.Grading
