-- Prove2me | solution 1 for GlobalTheory.PrimeElement.algebraMap_away_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:33.15508+00:00
-- url     : https://prove2.me/submissions/836edf10-10ab-499b-8093-3e8ac99ff02e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]
omit [(Ideal.span {π}).IsPrime]
namespace GlobalTheory.PrimeElement
theorem _root_.solution (hπ : π ≠ 0) : Function.Injective (algebraMap A K) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hinj := FaithfulSMul.algebraMap_injective R K
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers π) y
  have h := congrArg (algebraMap A K) (IsLocalization.mk'_spec A a s)
  rw [map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply, eq_comm,
    map_eq_zero_iff _ hinj] at h
  simp [h]
end GlobalTheory.PrimeElement
