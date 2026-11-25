-- Prove2me | solution 1 for GlobalTheory.algebraMap_mem_range_atPrime_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:21:01.73777+00:00
-- url     : https://prove2.me/submissions/703c5afb-7d46-4aee-8db4-c43011830bb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  [Algebra.FiniteType ℤ A]
variable {a : A} {S : Type*} [CommRing S] [Algebra A S] [IsLocalization.Away a S]
omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] [IsLocalization.Away a S]
namespace GlobalTheory
theorem _root_.solution (a : A) [IsLocalization.Away a S] (m : Ideal A) [m.IsPrime]
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m]
    (F : Type*) [Field F] [Algebra A F] [FaithfulSMul A F] [Algebra S F] [Algebra L F]
    [IsScalarTower A S F] [IsScalarTower A L F] (φ : S) :
    algebraMap S F φ ∈ (algebraMap L F).range ↔
      ∃ s ∉ m, ∃ b : A, algebraMap A S s * φ = algebraMap A S b := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj m.primeCompl z
    have hinj : Function.Injective (algebraMap S F) :=
      IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers a) S _ fun x hx => by
        rw [← IsScalarTower.algebraMap_apply] at hx
        rw [(FaithfulSMul.algebraMap_eq_zero_iff A F).mp hx, map_zero]
    refine ⟨s, s.2, b, hinj ?_⟩
    have e := congrArg (algebraMap L F) hbs
    rw [map_mul, hz, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, mul_comm, e]
  · rintro ⟨s, hs, b, hb⟩
    refine ⟨IsLocalization.mk' L b (⟨s, hs⟩ : m.primeCompl), ?_⟩
    have hs0 : algebraMap A F s ≠ 0 := by
      rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      rintro rfl
      exact hs m.zero_mem
    refine mul_left_cancel₀ hs0 ?_
    have e := congrArg (algebraMap S F) hb
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e
    rw [e, IsScalarTower.algebraMap_apply A L F s, ← map_mul, IsScalarTower.algebraMap_apply A L F b]
    exact congrArg _ (IsLocalization.mk'_spec' L b (⟨s, hs⟩ : m.primeCompl))
end GlobalTheory
