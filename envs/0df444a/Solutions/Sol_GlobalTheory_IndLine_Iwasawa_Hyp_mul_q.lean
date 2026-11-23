-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.mul_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:35.800156+00:00
-- url     : https://prove2.me/submissions/2f4d0e77-ac09-404e-8bfe-cbf21fa55d7f

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
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h
omit h
namespace GlobalTheory.IndLine.Iwasawa.Hyp
theorem _root_.solution (g : Matrix m m A) : g * prY c J x y = -Matrix.vecMulVec (g *ᵥ y) (J *ᵥ (c ∘ x)) := by
  rw [prY, Matrix.mul_neg, Matrix.mul_vecMulVec]
end GlobalTheory.IndLine.Iwasawa.Hyp
