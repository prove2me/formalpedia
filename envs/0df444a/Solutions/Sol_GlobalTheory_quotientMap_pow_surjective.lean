-- Prove2me | solution 1 for GlobalTheory.quotientMap_pow_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:35.4857+00:00
-- url     : https://prove2.me/submissions/cf49706f-6a07-4b3a-8c3c-f572158fc1ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_exists_sub_mem_pow_succ

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
namespace GlobalTheory
theorem _root_.solution (hle : I ≤ J.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ J)
    (h₁ : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ 2) (n : ℕ) :
    Function.Surjective (Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow_of_le hle n)) := by
  have key : ∀ b, ∃ a, φ a - b ∈ J ^ n := by
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      obtain ⟨x, -, hx⟩ := exists_sub_mem_pow_succ hle h₀ h₁ n _ ha
      refine ⟨a - x, ?_⟩
      have : φ (a - x) - b = -(φ x - (φ a - b)) := by
        rw [map_sub]; ring
      rw [this]
      exact neg_mem hx
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, ha⟩ := key b
  exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]; exact ha⟩
end GlobalTheory
