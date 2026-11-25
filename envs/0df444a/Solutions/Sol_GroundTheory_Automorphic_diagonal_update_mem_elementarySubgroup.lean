-- Prove2me | solution 1 for GroundTheory.Automorphic.diagonal_update_mem_elementarySubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:26:33.172009+00:00
-- url     : https://prove2.me/submissions/854ac53a-db7f-466a-82b9-9d023565aabf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
import Theorems.Thm_GroundTheory_Automorphic_transvectionGL_mem_elementarySubgroup
import Theorems.Thm_GroundTheory_Automorphic_transvection_mul_eq_diagonal_update
import Theorems.Thm_GroundTheory_Automorphic_coe_diagonalGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_diagonalGL

set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}
namespace GroundTheory.Automorphic
theorem _root_.solution (i j : n) (hij : i ≠ j) (u : Rˣ) :
    diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) ∈ elementarySubgroup n R := by
  have h : diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) =
      transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨j, i, hij.symm, -(↑u⁻¹ : R)⟩ *
        transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ *
          transvectionGL n R ⟨j, i, hij.symm, 1⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ := by
    ext1
    simp only [Units.val_mul, coe_transvectionGL, TransvectionStruct.toMatrix_mk, coe_diagonalGL]
    rw [transvection_mul_eq_diagonal_update i j hij u]
    congr 1
    funext k
    simp only [Pi.mul_apply, Units.val_mul, Function.update_apply, Pi.one_apply, Pi.mulSingle_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  rw [h]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact transvectionGL_mem_elementarySubgroup _
end GroundTheory.Automorphic
