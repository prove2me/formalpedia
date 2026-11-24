-- Prove2me | solution 1 for GlobalTheory.PrimeSection.zpow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:35.23517+00:00
-- url     : https://prove2.me/submissions/6f8d4e2e-aa9d-4f98-8c64-5646ce395199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
variable [IsLocallyNoetherian X]
namespace GlobalTheory.PrimeSection
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (ρ : A →+* B)
    (hρ : Function.Injective ρ) {σ u p : A} (hσ : IsUnit σ) (hu : IsUnit u) (hp : ¬ IsUnit p)
    (τ : Bˣ) (hτ : (τ : B) = ρ p) {n : ℤ} (h : ρ σ = (τ ^ n : Bˣ) * ρ u) : n = 0 := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => rfl
    | succ k =>
      exfalso
      have h' : ρ σ = ρ (p ^ (k + 1) * u) := by
        rw [h, map_mul, map_pow, ← hτ, zpow_natCast, Units.val_pow_eq_pow_val]
      have hσ' : IsUnit (p ^ (k + 1) * u) := hρ h' ▸ hσ
      exact hp ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_of_mul_isUnit_left hσ'))
  · cases k with
    | zero => simp
    | succ k =>
      exfalso
      have e : ((τ ^ (-((k + 1 : ℕ) : ℤ)) : Bˣ) : B) * ((τ ^ (k + 1) : Bˣ) : B) = 1 := by
        rw [← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel, Units.val_one]
      have h' : ρ (σ * p ^ (k + 1)) = ρ u := by
        rw [map_mul, map_pow, h, ← hτ, ← Units.val_pow_eq_pow_val, mul_right_comm, e, one_mul]
      have hu' : IsUnit (σ * p ^ (k + 1)) := (hρ h').symm ▸ hu
      exact hp ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_of_mul_isUnit_right hu'))
end GlobalTheory.PrimeSection
