-- Prove2me | solution 1 for GlobalTheory.T.commuting_integral_matrix_topnil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:17.972122+00:00
-- url     : https://prove2.me/submissions/e0646492-4353-467f-86f0-b8a99fcb1674

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Theorems.Thm_GlobalTheory_UnitDiscAlg_norm_lt_one_of_pow_of_commute


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → ∀ w : Matrix (Fin n) (Fin n) E, w * N = N * w → (∀ i j, ‖w i j‖ ≤ 1) → ∀ M : ℕ, (∀ i j, ‖(w ^ M) i j‖ < 1) → ∀ i j, ‖w i j‖ < 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | exact GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | (intros; apply GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute <;> assumption)
end _root_.GlobalTheory.T
