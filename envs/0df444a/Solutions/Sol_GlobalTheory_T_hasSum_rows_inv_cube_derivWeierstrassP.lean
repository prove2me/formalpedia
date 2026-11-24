-- Prove2me | solution 1 for GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:01.5822+00:00
-- url     : https://prove2.me/submissions/93e6f0e6-f0dd-4f58-84d3-c7a489764ec8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassPStatement
import Theorems.Thm_GlobalTheory_WpFam_hasSum_rows_derivWeierstrassP


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
theorem _root_.solution : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | exact GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP <;> assumption)
end _root_.GlobalTheory.T
