-- Prove2me | solution 1 for GlobalTheory.natCard_matrices_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:52.9218+00:00
-- url     : https://prove2.me/submissions/a0145d19-2b2c-46ce-8ff9-9e961b3f75ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NatCardMatricesMulEqZero

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
theorem _root_.solution (k : Type) [Field k] [Finite k] (m n j : ℕ)
    (A : Matrix (Fin n) (Fin n) k)
    (h : Module.finrank k (LinearMap.range A.mulVecLin) + j = n) :
    Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  have h1 : Module.finrank k (LinearMap.range (Aᵀ).mulVecLin)
      = Module.finrank k (LinearMap.range A.mulVecLin) := Matrix.rank_transpose A
  have h2 := LinearMap.finrank_range_add_finrank_ker (Aᵀ).mulVecLin
  rw [h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank k (LinearMap.ker (Aᵀ).mulVecLin) = j := by omega
  rw [Nat.card_congr (killersEquiv A), Nat.card_fun, Module.natCard_eq_pow_finrank (K := k), h3,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, pow_mul]
end GlobalTheory
