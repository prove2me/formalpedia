-- Prove2me | solution 1 for GlobalTheory.flat_of_surjective_quotient_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:18.989783+00:00
-- url     : https://prove2.me/submissions/d0c215d1-a9bf-47e2-ae5f-47cdfcdc98a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_flat_of_flat_quotientMap_pow
import Theorems.Thm_GlobalTheory_quotientMap_pow_bijective

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
theorem _root_.solution (hI : I ≤ Ideal.jacobson ⊥) (hle : I ≤ I.comap φ)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ I) (h₁ : ∀ y ∈ I, ∃ x ∈ I, φ x - y ∈ I ^ 2) : φ.Flat := by
  refine ringHom_flat_of_flat_quotientMap_pow φ ?_ hI (pow_le_comap_pow_of_le hle) fun n =>
    RingHom.Flat.of_bijective (quotientMap_pow_bijective hle h₀ h₁ n)
  refine le_antisymm (Ideal.map_le_of_le_comap hle)
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hI fun y hy => ?_)
  obtain ⟨x, hx, hxy⟩ := h₁ y hy
  rw [show y = φ x - (φ x - y) by ring]
  refine sub_mem (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hx)) (Submodule.mem_sup_right ?_)
  rwa [smul_eq_mul, ← pow_two]
end GlobalTheory
