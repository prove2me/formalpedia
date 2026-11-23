-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.prY_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:35.739943+00:00
-- url     : https://prove2.me/submissions/b20ac46c-8b77-4b85-bd5f-3e1371a7ad54

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
theorem _root_.solution (v : m → A) : prY c J x y *ᵥ v = -(v ⬝ᵥ J *ᵥ (c ∘ x)) • y := by
  rw [prY, Matrix.neg_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm, neg_smul, op_smul_eq_smul]
end GlobalTheory.IndLine.Iwasawa
