-- Prove2me | solution 1 for Matrix.finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ec409b5e-cb8d-5374-8efb-9cb54dd04ef8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {K : Type} [Field K] (T : Matrix (Fin 2) (Fin 2) K) (a b : K)
    (hT : (T - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (T - b • (1 : Matrix (Fin 2) (Fin 2) K)) = 0) (hab : a ≠ b) :
    (Module.finrank K (LinearMap.ker (Matrix.mulVecLin (T - a • (1 : Matrix (Fin 2) (Fin 2) K)))) = 1 ∧
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin (T - b • (1 : Matrix (Fin 2) (Fin 2) K)))) = 1) ↔
    ((T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 ∧ (T - b • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0) := by
  classical

  have hdet : ∀ M : Matrix (Fin 2) (Fin 2) K,
      M.det = 0 ↔ Module.finrank K ↥(LinearMap.ker M.mulVecLin) ≠ 0 := by
    intro M
    rw [Ne, Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv0, hv⟩
      exact ⟨v, by rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply], hv0⟩
    · rintro ⟨v, hv, hv0⟩
      exact ⟨v, hv0, by rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv⟩

  have hinf : LinearMap.ker (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).mulVecLin ⊓
      LinearMap.ker (T - b • (1 : Matrix (Fin 2) (Fin 2) K)).mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply] at hv
    have h2 : ((T - a • (1 : Matrix (Fin 2) (Fin 2) K)) - (T - b • (1 : Matrix (Fin 2) (Fin 2) K))).mulVec v = 0 := by
      rw [Matrix.sub_mulVec, hv.1, hv.2, sub_zero]
    rw [sub_sub_sub_cancel_left, ← sub_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hab)))

  have hsum : Module.finrank K ↥(LinearMap.ker (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).mulVecLin) +
      Module.finrank K ↥(LinearMap.ker (T - b • (1 : Matrix (Fin 2) (Fin 2) K)).mulVecLin) ≤ 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (T - a • (1 : Matrix (Fin 2) (Fin 2) K)).mulVecLin)
      (LinearMap.ker (T - b • (1 : Matrix (Fin 2) (Fin 2) K)).mulVecLin)
    rw [hinf, finrank_bot, add_zero] at h
    rw [← h]
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun K).le
  have ha := hdet (T - a • (1 : Matrix (Fin 2) (Fin 2) K))
  have hb := hdet (T - b • (1 : Matrix (Fin 2) (Fin 2) K))
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨ha.mpr (by rw [h1]; exact one_ne_zero), hb.mpr (by rw [h2]; exact one_ne_zero)⟩
  · rintro ⟨h1, h2⟩
    have h1' := ha.mp h1
    have h2' := hb.mp h2
    omega

end S_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero
end P2MW
export P2MW.S_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero (solution)
