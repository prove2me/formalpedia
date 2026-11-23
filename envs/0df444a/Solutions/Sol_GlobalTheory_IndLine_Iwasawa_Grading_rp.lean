-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.rp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:56.819801+00:00
-- url     : https://prove2.me/submissions/69969283-13b4-4790-8e75-3d99ce5f4f5f

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
theorem _root_.solution : r * p = 0 := by rw [h.sum, sub_mul, sub_mul, one_mul, h.pp, h.qp, sub_self, sub_zero]
end GlobalTheory.IndLine.Iwasawa.Grading
