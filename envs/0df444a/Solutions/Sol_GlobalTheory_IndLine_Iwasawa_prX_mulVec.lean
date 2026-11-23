-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.prX_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:29.755513+00:00
-- url     : https://prove2.me/submissions/1ae4866b-2876-4195-9c3f-1955d65a7bc4

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
namespace GlobalTheory.IndLine.Iwasawa
theorem _root_.solution (v : m → A) : prX c J x y *ᵥ v = (v ⬝ᵥ J *ᵥ (c ∘ y)) • x := by
  rw [prX, Matrix.vecMulVec_mulVec, dotProduct_comm, op_smul_eq_smul]
end GlobalTheory.IndLine.Iwasawa
