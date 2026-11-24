-- Prove2me | solution 1 for GlobalTheory.trace_transvection_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:37:46.321945+00:00
-- url     : https://prove2.me/submissions/78d40b2c-48e5-406b-9447-4fa9badc472e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace GlobalTheory
private theorem trace_mul_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (u w : n → ℚ) : (T * vecMulVec u w).trace = w ⬝ᵥ T.mulVec u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory
end

set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (x y : n → ℚ) (t : ℚ) :
    ((1 + t • vecMulVec x y)ᵀ * T * (1 + t • vecMulVec x y)).trace =
      T.trace + t * (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x) +
        t ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) := by
  have hP : (1 + t • vecMulVec x y)ᵀ = 1 + t • vecMulVec y x := by
    rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  rw [hP]
  have e : (1 + t • vecMulVec y x) * T * (1 + t • vecMulVec x y) =
      T + t • (T * vecMulVec x y) + t • (vecMulVec y x * T) + (t * t) • (vecMulVec y x * T * vecMulVec x y) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [e, trace_add, trace_add, trace_add, trace_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, Matrix.trace_mul_comm (vecMulVec y x) T]
  simp only [trace_mul_vecMulVec]
  rw [← Matrix.mulVec_mulVec]
  have hv : ∀ w : n → ℚ, vecMulVec y x *ᵥ w = (x ⬝ᵥ w) • y := by
    intro w
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv, dotProduct_smul, smul_eq_mul]
  ring
end GlobalTheory
