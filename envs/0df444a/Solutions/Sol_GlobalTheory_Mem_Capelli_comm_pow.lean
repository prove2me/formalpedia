-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.comm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:26.428799+00:00
-- url     : https://prove2.me/submissions/5a1c3649-8e31-47b3-848c-03eec264179e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
import Theorems.Thm_GlobalTheory_Mem_Capelli_comm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)
omit [Algebra ℂ A]
include hdd hdx
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution (p : ℕ) (a : Fin m) (l i j : Fin n) :
    D a l * ((X * D) ^ p) i j = ((X * D) ^ p) i j * D a l
      + ∑ r ∈ Finset.range p, ((X * D) ^ r) i l * (D * (X * D) ^ (p - (r + 1))) a j := by
  induction p generalizing i with
  | zero => by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ p ih =>
    have h1 : ∀ k, D a l * ((X * D) i k * ((X * D) ^ p) k j) =
        (X * D) i k * ((X * D) ^ p) k j * D a l
        + (∑ r ∈ Finset.range p, (X * D) i k * ((X * D) ^ r) k l * (D * (X * D) ^ (p - (r + 1))) a j
          + if i = l then D a k * ((X * D) ^ p) k j else 0) := fun k => by
      rw [← mul_assoc, comm_one X D hdd hdx, add_mul, mul_assoc, ih, mul_add, Finset.mul_sum, add_assoc]
      simp only [mul_assoc, ite_mul, zero_mul]
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ']
    simp only [h1, Finset.sum_add_distrib]
    congr 2
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, ← Matrix.mul_apply, ← pow_succ', Nat.add_sub_add_right]
    · by_cases h : i = l <;> simp [h, Matrix.one_apply, Matrix.mul_apply]
end GlobalTheory.Mem.Capelli
