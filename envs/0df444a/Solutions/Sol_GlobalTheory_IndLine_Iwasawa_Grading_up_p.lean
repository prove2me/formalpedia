-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.up_p
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:41.764049+00:00
-- url     : https://prove2.me/submissions/e3ff6a0e-e777-4f1d-8beb-bf153293b448
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_rp

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
theorem _root_.solution (Z : R) : up p r q Z * p = 0 := by
  simp only [up, add_mul, mul_assoc, h.rp, h.qp, mul_zero, add_zero]
end GlobalTheory.IndLine.Iwasawa.Grading
