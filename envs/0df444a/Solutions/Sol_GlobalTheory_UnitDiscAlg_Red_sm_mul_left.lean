-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.Red.sm_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:54.479935+00:00
-- url     : https://prove2.me/submissions/7b068c93-2de6-4400-9508-d32882ac589b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
import Theorems.Thm_P2M_GlobalTheory_UnitDiscAlg_Red_norm_sum_lt_one__cfa7b69ad7f8

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
theorem _root_.solution {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : Sm y) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hx i k)) (hy k j))
end GlobalTheory.UnitDiscAlg.Red
