-- Prove2me | solution 1 for GlobalTheory.transpose_mul_add_mul_map_eq_zero_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:50.98851+00:00
-- url     : https://prove2.me/submissions/8eeebdbb-395e-4dbb-8e5e-cf81b21d869e

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
    (S X Y : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]
end GlobalTheory
