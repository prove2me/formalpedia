-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.qp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:54.331898+00:00
-- url     : https://prove2.me/submissions/16734d5b-aece-4ffd-b978-da7e82c7a2d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_qx
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_mul_p

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
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h
namespace GlobalTheory.IndLine.Iwasawa.Hyp
theorem _root_.solution : prY c J x y * prX c J x y = 0 := by rw [mul_p, h.qx, Matrix.zero_vecMulVec]
end GlobalTheory.IndLine.Iwasawa.Hyp
