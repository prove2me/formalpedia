-- Prove2me | solution 1 for GlobalTheory.CommTriang.isUnit_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:44.608795+00:00
-- url     : https://prove2.me/submissions/a102400e-f53e-487f-bf69-c25332a2c511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
import Theorems.Thm_GlobalTheory_CommTriang_blockOne_mul
import Theorems.Thm_GlobalTheory_CommTriang_blockOne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CommTriang
open Matrix
namespace GlobalTheory.CommTriang
theorem _root_.solution {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) (hQ : IsUnit Q) :
    IsUnit (blockOne Q) ∧ (blockOne Q)⁻¹ = blockOne Q⁻¹ := by
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have h : blockOne Q * blockOne Q⁻¹ = 1 := by
    rw [blockOne_mul, Matrix.mul_nonsing_inv _ hQd, blockOne_one]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h), Matrix.inv_eq_right_inv h⟩
end GlobalTheory.CommTriang
