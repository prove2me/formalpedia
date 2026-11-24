-- Prove2me | solution 1 for GlobalTheory.T.G2_add_weierstrassP_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:50.823468+00:00
-- url     : https://prove2.me/submissions/0ad6362f-6d69-4330-9b30-51d6aa31930c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSumStatement
import Theorems.Thm_GlobalTheory_WpFam_hasSum_rows_G2_add_weierstrassP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 2) (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | exact GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP <;> assumption)
end _root_.GlobalTheory.T
