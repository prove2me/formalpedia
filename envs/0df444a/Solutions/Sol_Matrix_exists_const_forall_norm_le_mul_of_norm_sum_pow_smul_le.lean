-- Prove2me | solution 1 for Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6afba6ad-69f1-5158-a676-83cee7e421f2

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le

set_option autoImplicit false

theorem solution
    (L : ℕ) (x : Fin L → ℂ) (hx : Function.Injective x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (v : Fin L → E) (B : ℝ),
      (∀ t : Fin L, ‖∑ m : Fin L, (x t) ^ (m : ℕ) • v m‖ ≤ B) → ∀ m : Fin L, ‖v m‖ ≤ C * B := by
  classical
  set V : Matrix (Fin L) (Fin L) ℂ := Matrix.vandermonde x with hV
  have hdet : V.det ≠ 0 := by rw [hV]; exact Matrix.det_vandermonde_ne_zero_iff.2 hx
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.2 hdet
  set W : Matrix (Fin L) (Fin L) ℂ := V⁻¹ with hW
  have hWV : W * V = 1 := by rw [hW]; exact Matrix.nonsing_inv_mul V hunit
  refine ⟨∑ m : Fin L, ∑ t : Fin L, ‖W m t‖, by positivity, ?_⟩
  intro E _ _ v B hB m

  have hrec : ∑ t : Fin L, W m t • (∑ m' : Fin L, (x t) ^ (m' : ℕ) • v m') = v m := by
    have : ∀ t m' : Fin L, (x t) ^ (m' : ℕ) = V t m' := fun t m' => by rw [hV, Matrix.vandermonde_apply]
    simp_rw [this, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ m' : Fin L, ∑ t : Fin L, (W m t * V t m') • v m' = ((W * V) m m') • v m' := fun m' => by
      rw [← Finset.sum_smul, Matrix.mul_apply]
    simp_rw [this, hWV, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB m)
  calc ‖v m‖ = ‖∑ t : Fin L, W m t • (∑ m' : Fin L, (x t) ^ (m' : ℕ) • v m')‖ := by rw [hrec]
    _ ≤ ∑ t : Fin L, ‖W m t • (∑ m' : Fin L, (x t) ^ (m' : ℕ) • v m')‖ := norm_sum_le _ _
    _ ≤ ∑ t : Fin L, ‖W m t‖ * B := Finset.sum_le_sum fun t _ => by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
    _ = (∑ t : Fin L, ‖W m t‖) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ m : Fin L, ∑ t : Fin L, ‖W m t‖) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact Finset.single_le_sum (f := fun m => ∑ t : Fin L, ‖W m t‖) (fun _ _ => by positivity) (Finset.mem_univ m)

end S_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
end P2MW
export P2MW.S_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le (solution)
