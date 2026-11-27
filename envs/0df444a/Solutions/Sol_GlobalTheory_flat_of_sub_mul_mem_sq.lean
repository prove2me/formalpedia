-- Prove2me | solution 1 for GlobalTheory.flat_of_sub_mul_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:05.254534+00:00
-- url     : https://prove2.me/submissions/14083f3c-d762-461e-b2b5-5d819f20f71d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_flat_of_surjective_quotient_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
variable [IsNoetherianRing A] {φ : A →+* A}
namespace GlobalTheory
theorem _root_.solution [IsLocalRing A] (hle : maximalIdeal A ≤ (maximalIdeal A).comap φ)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) {c : A} (hc : IsUnit c)
    (h₁ : ∀ x ∈ maximalIdeal A, φ x - c * x ∈ maximalIdeal A ^ 2) : φ.Flat := by
  refine flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀ fun y hy => ?_
  obtain ⟨u, rfl⟩ := hc
  have hx : (↑u⁻¹ : A) * y ∈ maximalIdeal A := Ideal.mul_mem_left _ _ hy
  exact ⟨_, hx, by simpa using h₁ _ hx⟩
end GlobalTheory
