-- Prove2me | solution 1 for GlobalTheory.PrimeElement.exists_unit_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:20:37.640184+00:00
-- url     : https://prove2.me/submissions/7471ab81-1b39-43b7-9530-5358bb07b98c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Theorems.Thm_GlobalTheory_PrimeElement_exists_algebraMap_eq

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
variable {A S}
namespace GlobalTheory.PrimeElement
theorem _root_.solution (hπ : π ≠ 0) {y : A} (hy : IsUnit y) {z : S} (hz : IsUnit z)
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  have h' : algebraMap A K (y⁻¹ : Aˣ) = algebraMap S K (z⁻¹ : Sˣ) := by
    refine mul_left_cancel₀ (y.isUnit.map (algebraMap A K)).ne_zero ?_
    rw [← map_mul, Units.mul_inv, map_one, h, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨r, hr⟩ := exists_algebraMap_eq K hπ h
  obtain ⟨r', hr'⟩ := exists_algebraMap_eq K hπ h'
  refine ⟨r, IsUnit.of_mul_eq_one r' (FaithfulSMul.algebraMap_injective R K ?_), hr⟩
  rw [IsScalarTower.algebraMap_apply R A K, map_mul, hr, hr', Units.mul_inv, map_one, map_one]
end GlobalTheory.PrimeElement
