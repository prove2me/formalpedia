-- Prove2me | solution 1 for GlobalTheory.ringSeminorm_adjugate_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:47.002811+00:00
-- url     : https://prove2.me/submissions/cb24f952-ea50-4563-80f3-16acfe0dae6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_ringSeminorm_det_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C)
    (i j : Fin (n + 1)) : ν (H.adjugate i j) ≤ n ! * C ^ n := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have h := ringSeminorm_det_le ν h1 (H.submatrix j.succAbove i.succAbove) (C := C)
    fun _ _ => hH _ _
  rw [Fintype.card_fin] at h
  rcases neg_one_pow_eq_or R ((j : ℕ) + i) with hs | hs
  · rw [hs, one_mul]; exact h
  · rw [hs, neg_one_mul, map_neg_eq_map]; exact h
end GlobalTheory
