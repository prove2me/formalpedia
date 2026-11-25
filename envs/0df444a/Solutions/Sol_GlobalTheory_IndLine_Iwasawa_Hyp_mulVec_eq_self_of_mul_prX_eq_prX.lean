-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.mulVec_eq_self_of_mul_prX_eq_prX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:36.661775+00:00
-- url     : https://prove2.me/submissions/b85878fd-c3d8-4ef7-ad0a-562d4188a6ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_px

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
theorem _root_.solution {g : Matrix m m A} (hg : g * prX c J x y = prX c J x y) : g *ᵥ x = x := by
  rw [← h.px, Matrix.mulVec_mulVec, hg]
end GlobalTheory.IndLine.Iwasawa.Hyp
