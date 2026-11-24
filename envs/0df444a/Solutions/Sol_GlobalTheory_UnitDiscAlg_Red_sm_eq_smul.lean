-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.Red.sm_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:53.287411+00:00
-- url     : https://prove2.me/submissions/8bcc4207-bbe3-436a-8031-9fe6cf364303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.UnitDiscAlg.Red
theorem _root_.solution {N s : Matrix (Fin n) (Fin n) E} {ϖ : E} (h0 : 0 < ‖ϖ‖)
    (hu : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) (hs : Sm s) (hc : s * N = N * s) :
    ∃ a : Matrix (Fin n) (Fin n) E, a * N = N * a ∧ (∀ i j, ‖a i j‖ ≤ 1) ∧ s = ϖ • a := by
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp h0
  refine ⟨ϖ⁻¹ • s, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ h0, mul_one]
    exact hu _ (hs i j)
  · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]
end GlobalTheory.UnitDiscAlg.Red
