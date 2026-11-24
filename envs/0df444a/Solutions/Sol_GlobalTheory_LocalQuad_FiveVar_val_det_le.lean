-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.val_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:15.954665+00:00
-- url     : https://prove2.me/submissions/044aa2a2-9a6d-4cb2-8bd7-2f88677cf5d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_val_bf_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (P : Matrix n n K) :
    v (∏ i, 2 * a i) * v P.det ^ 2 ≤ ∏ i, v (qf a (P i)) := by
  have hB : P * Matrix.diagonal (fun i => 2 * a i) * Pᵀ =
      Matrix.of fun i j => bf a (P i) (P j) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, bf]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hd := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  have e : v (∏ i, 2 * a i) * v P.det ^ 2 = v (P.det * (∏ i, 2 * a i) * P.det) := by
    rw [map_mul, map_mul, sq, mul_comm (v P.det) (v (∏ i, 2 * a i)), mul_assoc]
  rw [e, hd, Matrix.det_apply']
  apply Valuation.map_sum_le
  intro σ _
  have hε : v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [map_mul, hε, one_mul, map_prod]
  apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
  rw [← Finset.prod_pow]
  calc ∏ i, v (Matrix.of (fun i j => bf a (P i) (P j)) (σ i) i) ^ 2
      ≤ ∏ i, (v (qf a (P (σ i))) * v (qf a (P i))) :=
        Finset.prod_le_prod' fun i _ => val_bf_sq_le h2 v hsq a han _ _
    _ = (∏ i, v (qf a (P i))) ^ 2 := by
        rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => v (qf a (P i))), sq]
end GlobalTheory.LocalQuad.FiveVar
