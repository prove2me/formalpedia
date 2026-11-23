-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.mul_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:57.47552+00:00
-- url     : https://prove2.me/submissions/5144c4bf-5d5c-4df8-89bd-edfb7506c690

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
theorem _root_.solution (g : Matrix m m A) : g * prX c J x y = Matrix.vecMulVec (g *ᵥ x) (J *ᵥ (c ∘ y)) := by
  rw [prX, Matrix.mul_vecMulVec]
end GlobalTheory.IndLine.Iwasawa.Hyp
