-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.pr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:35.127412+00:00
-- url     : https://prove2.me/submissions/de85975f-3b77-4256-b756-ff8f84bd9a75

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
theorem _root_.solution : p * r = 0 := by rw [h.sum, mul_sub, mul_sub, mul_one, h.pp, h.pq, sub_self, sub_zero]
end GlobalTheory.IndLine.Iwasawa.Grading
