-- Prove2me | solution 1 for GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:32.435261+00:00
-- url     : https://prove2.me/submissions/432adce5-6f69-4ca3-81e0-fc16ab814024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LiftHasSumZeroOfSurjectiveModPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LiftHasSumZeroOfSurjectiveModPrimeStatement
import Theorems.Thm_GlobalTheory_lift_hasSum_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (X ι : Type) (η : X → ι → ℂ_[l]) (τ : ι → ℝ) (S : Set X), (∀ t : ι → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∀ x ∈ S, (∀ i, ‖η x i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∃ y : ℕ → X, y 0 = x ∧ (∀ k, y k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) 0 := by
  first | exact @GlobalTheory.lift_hasSum_zero | exact GlobalTheory.lift_hasSum_zero | (intros; apply GlobalTheory.lift_hasSum_zero <;> assumption)
end _root_.GlobalTheory.T
