-- Prove2me | solution 1 for GlobalTheory.flag_basisMulGL_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:07:21.644389+00:00
-- url     : https://prove2.me/submissions/111b48fc-1021-4a0a-872d-a8a20e8dfafd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_mem_upperTriangularGL
import Theorems.Thm_GlobalTheory_flag_basisMulGL_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (b : Basis (Fin n) R M) (g : GL (Fin n) R) :
    (basisMulGL b g).flag = b.flag ↔ g ∈ upperTriangularGL (Fin n) R := by
  constructor
  · intro h
    rw [mem_upperTriangularGL]
    intro i j hij
    have hj : basisMulGL b g j ∈ b.flag j.succ := by
      rw [← h]
      exact Basis.self_mem_flag _ Fin.castSucc_lt_succ
    rw [← toMatrix_basisMulGL b g, Basis.toMatrix_apply]
    exact (mem_basis_flag_iff b _ _).mp hj i (Fin.succ_le_castSucc_iff.mpr hij)
  · intro hg
    funext k
    refine le_antisymm (flag_basisMulGL_le b hg k) ?_
    have h := flag_basisMulGL_le (basisMulGL b g) (inv_mem hg) k
    rwa [← basisMulGL_mul, mul_inv_cancel, basisMulGL_one] at h
end GlobalTheory
