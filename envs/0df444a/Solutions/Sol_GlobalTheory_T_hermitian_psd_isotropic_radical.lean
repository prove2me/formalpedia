-- Prove2me | solution 1 for GlobalTheory.T.hermitian_psd_isotropic_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:34.629137+00:00
-- url     : https://prove2.me/submissions/e8ccbd55-7e50-4419-9d1d-60f8b3e1976a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianPsdIsotropicRadical
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianPsdIsotropicRadicalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermitianForm_pairing_eq_zero_of_psd


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | exact GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | (intros; apply GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd <;> assumption)
end _root_.GlobalTheory.T
