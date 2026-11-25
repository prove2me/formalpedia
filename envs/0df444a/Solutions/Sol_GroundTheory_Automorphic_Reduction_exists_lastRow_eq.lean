-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_lastRow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:57.37885+00:00
-- url     : https://prove2.me/submissions/6ef282e6-9da8-4cfb-af7c-8611bf70485c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Theorems.Thm_GroundTheory_Automorphic_Reduction_coe_blockOneHom
import Theorems.Thm_GroundTheory_Automorphic_Reduction_det_rowMatrix
import Theorems.Thm_GroundTheory_Automorphic_Reduction_single_last_vecMul_rowMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Reduction.coe_blockOneHom

set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction
variable {F : Type*} [Field F] {m : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {x : Fin (m + 1) → F} (hx : x ≠ 0) :
    ∃ γ : GL (Fin (m + 1)) F,
      Pi.single (Fin.last m) 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = x := by
  classical

  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun j => not_not.1 fun hj => h ⟨j, hj⟩)
  by_cases hl : x (Fin.last m) ≠ 0
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x) (by rw [det_rowMatrix]; exact hl), ?_⟩
    exact single_last_vecMul_rowMatrix x
  · rw [not_not] at hl
    have hjl : j ≠ Fin.last m := fun h => hj (h ▸ hl)
    set τ := transvection j (Fin.last m) (1 : F) with hτ
    have hτdet : τ.det = 1 := det_transvection_of_ne j (Fin.last m) hjl 1
    set x' := x ᵥ* τ with hx'
    have hx'l : x' (Fin.last m) = x j := by
      simp [hx', hτ, transvection, vecMul_add, hl, Matrix.vecMul, dotProduct,
        Matrix.single_apply]
    have hx'l0 : x' (Fin.last m) ≠ 0 := by rw [hx'l]; exact hj
    set τu : GL (Fin (m + 1)) F :=
      GeneralLinearGroup.mkOfDetNeZero τ (by rw [hτdet]; exact one_ne_zero) with hτu
    refine ⟨GeneralLinearGroup.mkOfDetNeZero (rowMatrix x') (by rw [det_rowMatrix]; exact hx'l0) *
      τu⁻¹, ?_⟩
    rw [Units.val_mul, ← vecMul_vecMul]
    change (Pi.single (Fin.last m) 1 ᵥ* rowMatrix x') ᵥ* _ = x
    have hτu' : (τu : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = τ := rfl
    rw [single_last_vecMul_rowMatrix, hx', ← hτu', vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, vecMul_one]
end GroundTheory.Automorphic.Reduction
