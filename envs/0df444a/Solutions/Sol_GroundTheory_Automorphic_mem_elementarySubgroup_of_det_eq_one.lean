-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_elementarySubgroup_of_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:35.376124+00:00
-- url     : https://prove2.me/submissions/5abba421-7fd5-4539-a4f6-13a13a6abded

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
import Theorems.Thm_GroundTheory_Automorphic_coe_list_prod_transvectionGL
import Theorems.Thm_GroundTheory_Automorphic_list_prod_transvectionGL_mem
import Theorems.Thm_GroundTheory_Automorphic_coe_diagonalGL
import Theorems.Thm_GroundTheory_Automorphic_diagonalGL_mem_elementarySubgroup
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
variable {F : Type*} [Field F]
namespace GroundTheory.Automorphic
theorem _root_.solution {g : GL n F}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : g ∈ elementarySubgroup n F := by
  classical
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix n n F)
  have hdet : ∏ k, D k = 1 := by
    have h1 : (g : Matrix n n F).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]
    rw [hM, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, det_diagonal, one_mul, mul_one] at h1
    exact h1
  have hD : ∀ k, D k ≠ 0 := fun k h0 => by
    have := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hdet] at this
    exact one_ne_zero this
  let d : n → Fˣ := fun k => Units.mk0 (D k) (hD k)
  have hd : ∏ k, d k = 1 := by
    ext
    simp [d, Units.coe_prod, hdet]
  have hg' : g = (L.map (transvectionGL n F)).prod * diagonalGL d *
      (L'.map (transvectionGL n F)).prod := by
    ext1
    simp only [Units.val_mul, coe_list_prod_transvectionGL, coe_diagonalGL]
    rw [hM]
    rfl
  rw [hg']
  exact mul_mem (mul_mem (list_prod_transvectionGL_mem L) (diagonalGL_mem_elementarySubgroup hd))
    (list_prod_transvectionGL_mem L')
end GroundTheory.Automorphic
