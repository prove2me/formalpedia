-- Prove2me | solution 1 for GlobalTheory.HermWitt.dotProduct_congr_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:57.997795+00:00
-- url     : https://prove2.me/submissions/012a979d-5cc5-4b2d-acae-54fac9dc285a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution {m : Type*} [Fintype m] (c : E →+* E) (G : Matrix n n E)
    (P : Matrix n m E) (x y : m → E) :
    x ⬝ᵥ (Pᵀ * G * P.map c) *ᵥ (c ∘ y) = (P *ᵥ x) ⬝ᵥ G *ᵥ (c ∘ (P *ᵥ y)) := by
  have h : c ∘ (P *ᵥ y) = P.map c *ᵥ (c ∘ y) := funext fun i => RingHom.map_mulVec c P y i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
end GlobalTheory.HermWitt
