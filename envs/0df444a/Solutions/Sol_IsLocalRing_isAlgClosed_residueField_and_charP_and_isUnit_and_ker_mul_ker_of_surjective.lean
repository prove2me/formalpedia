-- Prove2me | solution 1 for IsLocalRing.isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ee49fbfd-5a5c-54d1-8c81-08dc772085b1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective

set_option autoImplicit false

open IsLocalRing

universe u

theorem solution
    {B B' : Type u} [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']
    (σ : B' →+* B) (hσ : Function.Surjective σ) (hsmall : RingHom.ker σ * maximalIdeal B' = ⊥)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p] [IsAlgClosed (ResidueField B)]
    (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime] (hpq : p ≠ q) (hpq' : p ≠ q') :
    IsAlgClosed (ResidueField B') ∧ CharP (ResidueField B') p ∧
      IsUnit ((q * q' : ℕ) : B') ∧ RingHom.ker σ * RingHom.ker σ = ⊥ := by
  haveI : IsLocalHom σ := IsLocalHom.of_surjective σ hσ

  let ρ : ResidueField B' →+* ResidueField B := ResidueField.map σ
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨b', rfl⟩ := hσ b
    exact ⟨residue B' b', rfl⟩
  have hρbij : Function.Bijective ρ := ⟨ρ.injective, hρsurj⟩
  let e : ResidueField B' ≃+* ResidueField B := RingEquiv.ofBijective ρ hρbij
  have hchar : CharP (ResidueField B') p := (RingHom.charP_iff_charP ρ p).mpr inferInstance
  refine ⟨IsAlgClosed.of_ringEquiv (ResidueField B) (ResidueField B') e.symm, hchar, ?_, ?_⟩
  ·
    haveI := hchar
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_mul]
    have hq : ((q : ℕ) : ResidueField B') ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ResidueField B') p q]
      exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)
    have hq' : ((q' : ℕ) : ResidueField B') ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ResidueField B') p q']
      exact fun h => hpq' ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)
    exact mul_ne_zero hq hq'
  ·
    have hle : RingHom.ker σ ≤ maximalIdeal B' := le_maximalIdeal (RingHom.ker_ne_top σ)
    refine le_bot_iff.mp ?_
    calc RingHom.ker σ * RingHom.ker σ ≤ RingHom.ker σ * maximalIdeal B' := Ideal.mul_mono_right hle
      _ = ⊥ := hsmall

end S_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective
end P2MW
export P2MW.S_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective (solution)
