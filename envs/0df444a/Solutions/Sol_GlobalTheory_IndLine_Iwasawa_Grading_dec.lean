-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Grading.dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:45.255099+00:00
-- url     : https://prove2.me/submissions/d4bce681-a486-4e4c-80df-995982fdb223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_conj_low

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
theorem _root_.solution (Z : R) : Z = up p r q (Z - θ * Z * θ) + mid p r q Z + (low p r q Z + θ * low p r q Z * θ) := by
  rw [h.conj_low]
  have e : p + r + q = 1 := by rw [h.sum]; abel
  calc Z = (p + r + q) * Z * (p + r + q) := by rw [e, one_mul, mul_one]
    _ = _ := by simp only [up, mid, low]; noncomm_ring
end GlobalTheory.IndLine.Iwasawa.Grading
