-- Prove2me | solution 1 for GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.555235+00:00
-- url     : https://prove2.me/submissions/68537860-de57-4c71-9572-9faa29ec2fba

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
namespace GlobalTheory.PrimeElement
theorem _root_.solution {S K : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] {ϖ : S}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃! a : ℤ, ∃ u : S, IsUnit u ∧ algebraMap S K u = algebraMap S K ϖ ^ a * x := by
  have hinj := IsFractionRing.injective S K
  have h0 : algebraMap S K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ (a b : ℤ) (u v : S), IsUnit v → algebraMap S K u = algebraMap S K ϖ ^ a * x →
      algebraMap S K v = algebraMap S K ϖ ^ b * x → b ≤ a := by
    intro a b u v hv h₁ h₂
    by_contra! hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + (n + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
    have : v = ϖ * (ϖ ^ n * u) := hinj <| by
      rw [h₂, hn, zpow_add₀ h0, zpow_natCast, map_mul, map_mul, map_pow, h₁]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hv))
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine existsUnique_of_exists_of_unique ⟨(n : ℤ) - m, (u * v⁻¹ : Sˣ), Units.isUnit _, ?_⟩ ?_
  · have hv : algebraMap S K v ≠ 0 := (v.isUnit.map _).ne_zero
    rw [zpow_sub₀ h0]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_natCast]
    field_simp
  · rintro a b ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩
    exact le_antisymm (key b a v u hu h₂ h₁) (key a b u v hv h₁ h₂)
end GlobalTheory.PrimeElement
