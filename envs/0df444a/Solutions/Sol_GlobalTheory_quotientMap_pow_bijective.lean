-- Prove2me | solution 1 for GlobalTheory.quotientMap_pow_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:58.988799+00:00
-- url     : https://prove2.me/submissions/ee20d253-4763-4ae4-833a-6398a11b00ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_injective_of_surjective
import Theorems.Thm_GlobalTheory_quotientMap_pow_surjective

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
theorem _root_.solution (hle : I ≤ I.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ I)
    (h₁ : ∀ y ∈ I, ∃ x ∈ I, φ x - y ∈ I ^ 2) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (I ^ n) φ (pow_le_comap_pow_of_le hle n)) :=
  ⟨ringHom_injective_of_surjective _ (quotientMap_pow_surjective hle h₀ h₁ n),
    quotientMap_pow_surjective hle h₀ h₁ n⟩
end GlobalTheory
