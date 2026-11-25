-- Prove2me | solution 1 for GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:52.132683+00:00
-- url     : https://prove2.me/submissions/6bae4c11-effc-43a7-a027-d5cd8d10674c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplexStatement
import Theorems.Thm_GlobalTheory_shortExact_mul_p_modP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  first | exact @GlobalTheory.shortExact_mul_p_modP | exact GlobalTheory.shortExact_mul_p_modP | (intros; apply GlobalTheory.shortExact_mul_p_modP <;> assumption)
end _root_.GlobalTheory.T
