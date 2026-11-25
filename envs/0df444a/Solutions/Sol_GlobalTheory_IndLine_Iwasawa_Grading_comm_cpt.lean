-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.comm_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:39.898086+00:00
-- url     : https://prove2.me/submissions/4486d51b-ce14-489a-a432-0e9712e91585

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
theorem _root_.solution (Z : R) : Commute (low p r q Z + θ * low p r q Z * θ) θ := by
  change _ * _ = _ * _
  rw [add_mul, mul_add, mul_assoc _ θ θ, h.θθ, mul_one, ← mul_assoc θ, ← mul_assoc θ, h.θθ, one_mul, add_comm]
end GlobalTheory.IndLine.Iwasawa.Grading
