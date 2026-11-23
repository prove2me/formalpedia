-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.c_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:06.350057+00:00
-- url     : https://prove2.me/submissions/edd585db-98fc-4e2b-98c6-9230f899b356

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
theorem _root_.solution (cc : ∀ a, c (c a) = a) (skew : J.map c = -Jᵀ) (v : m → A) : c ∘ (J *ᵥ (c ∘ v)) = -(v ᵥ* J) := by
  rw [map_mulVec' (c' := c) c (fun _ => rfl), skew, Matrix.neg_mulVec, Matrix.mulVec_transpose]
  congr 2
  funext i
  exact cc _
end GlobalTheory.IndLine.Iwasawa
