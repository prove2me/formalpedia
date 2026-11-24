-- Prove2me | solution 1 for GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:15.205931+00:00
-- url     : https://prove2.me/submissions/aac54d7f-91aa-40b3-8111-01e3d8b4a2ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassP
import Theorems.Thm_GlobalTheory_WpFam_hasSum_prod_derivWeierstrassP

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
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum
end GlobalTheory.WpFam
