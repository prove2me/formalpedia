-- Prove2me | solution 1 for GlobalTheory.T.finite_of_bijective_pairing_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:28.039388+00:00
-- url     : https://prove2.me/submissions/4a8911e2-afb5-4467-bf1e-362dacf4745d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmodStatement
import Theorems.Thm_GlobalTheory_finite_of_perfect_pairing_zmod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A] [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C] [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C), Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  first | exact @GlobalTheory.finite_of_perfect_pairing_zmod | exact GlobalTheory.finite_of_perfect_pairing_zmod | (intros; apply GlobalTheory.finite_of_perfect_pairing_zmod <;> assumption)
end _root_.GlobalTheory.T
