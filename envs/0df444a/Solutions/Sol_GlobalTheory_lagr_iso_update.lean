-- Prove2me | solution 1 for GlobalTheory.lagr_iso_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:38.838101+00:00
-- url     : https://prove2.me/submissions/666c07d9-7a58-4825-b2e4-ef5d67587653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C X : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = 0 := by
  have e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c =
      (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]
end GlobalTheory
