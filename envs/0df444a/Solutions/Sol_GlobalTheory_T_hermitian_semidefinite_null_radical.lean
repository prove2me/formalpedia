-- Prove2me | solution 1 for GlobalTheory.T.hermitian_semidefinite_null_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:37.028885+00:00
-- url     : https://prove2.me/submissions/8fefaaf8-9c42-4cf3-a5fb-feb9e545a169

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadical
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadicalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Herm_apply_eq_zero_of_isotropic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ x, (B x x).re = 0 → ∀ w, B x w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | exact GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | (intros; apply GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic <;> assumption)
end _root_.GlobalTheory.T
