-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:48.103778+00:00
-- url     : https://prove2.me/submissions/75708756-bb62-493b-a5f2-d8de9bc81b0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RTensorPairingEqZeroOfFlipInjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RTensorPairingEqZeroOfFlipInjectiveStatement
import Theorems.Thm_GlobalTheory_rTensor_pairing_eq_zero_of_flip_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  first | exact @GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective | exact GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective | (intros; apply GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective <;> assumption)
end _root_.GlobalTheory.T
