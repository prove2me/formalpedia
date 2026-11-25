-- Prove2me | solution 1 for GlobalTheory.associated_of_associated_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:52.809806+00:00
-- url     : https://prove2.me/submissions/40dd954c-6b42-4d09-acbe-dbc3320654fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Theorems.Thm_GlobalTheory_valuationRing_exists_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O K V : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    [CommRing V] [IsDomain V] [ValuationRing V] (φ : O →+* V) (b : V) (hb : b ≠ 0) (p q : O)
    {i j : ℕ} (hij : i < j) (hp : φ p ≠ 0) (hq : φ q ≠ 0)
    (h : Associated (φ p * b ^ i) (φ q * b ^ j)) : ∃ π : O, Associated b (φ π) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have h1 : Associated (φ p) (φ q * b ^ (k + 1)) := by
    refine Associated.of_mul_right (b := b ^ i) (d := b ^ i) ?_ (Associated.refl _)
      (pow_ne_zero _ hb)
    have e : φ q * b ^ (k + 1) * b ^ i = φ q * b ^ (i + k + 1) := by ring
    rwa [e]
  rcases ValuationRing.dvd_total p q with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h2 : Associated 1 (φ c * b ^ (k + 1)) := by
      refine Associated.of_mul_left (a := φ p) (c := φ p) ?_ (Associated.refl _) hp
      rwa [mul_one, ← mul_assoc, ← map_mul]
    have h3 : IsUnit (b ^ (k + 1)) := isUnit_of_mul_isUnit_right (associated_one_iff_isUnit.1 h2.symm)
    refine ⟨1, ?_⟩
    rw [map_one, associated_one_iff_isUnit]
    exact (isUnit_pow_iff (Nat.succ_ne_zero k)).1 h3
  · have h2 : Associated (φ c) (b ^ (k + 1)) := by
      refine Associated.of_mul_left (a := φ q) (c := φ q) ?_ (Associated.refl _) hq
      rwa [← map_mul]
    obtain ⟨r, rfl⟩ := valuationRing_exists_pow_eq O K c (Nat.succ_pos k)
    rw [map_pow] at h2
    exact ⟨r, ((Associated.pow_iff (Nat.succ_ne_zero k)).1 h2).symm⟩
end GlobalTheory
