-- Prove2me | solution 1 for ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/da930416-156a-5efa-b537-df69ad4c14e7

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Theorems.Thm_rademacher_phi_level_congruence
import Theorems.Thm_ModularCurve_eisensteinNumerator_dvd_mul_of_witness
import Theorems.Thm_dedekindSum_jacobiSym_mod_eight
import Theorems.Thm_rademacher_phi_level_witness_mod_oneTwenty_eq_one
import Theorems.Thm_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine

set_option autoImplicit false

open scoped NumberTheorySymbols

namespace WN120

open ModularCurve

private lemma modEq_helper (ℓ : ℕ) (a d t : ℤ) (h : a * d = 1 + t * ℓ) :
    Int.ModEq ((ℓ * 1 : ℕ) : ℤ) (a * d) 1 :=
  Int.modEq_iff_dvd.2 ⟨-t, by push_cast; linear_combination -h⟩

private lemma coprime_two_odd (r : ℕ) : Nat.Coprime 2 (2 * r + 1) := by
  rw [Nat.coprime_comm]
  unfold Nat.Coprime
  rw [show 2 * r + 1 = 1 + r * 2 from by ring, Nat.gcd_add_mul_right_left]
  decide

theorem exists_odd_witness (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h8 : ℓ % 8 = 1) (h12 : ℓ % 12 = 1) :
    ∃ a d z : ℤ, Int.ModEq ((ℓ * 1 : ℕ) : ℤ) (a * d) 1 ∧
      12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * 1 : ℕ) : ℚ)) + dedekindSum d 1
        - dedekindSum d (ℓ * 1)) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z ∧ Odd z := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩

  obtain ⟨x, hx⟩ : ∃ x : ZMod ℓ, quadraticChar (ZMod ℓ) x = -1 := by
    apply quadraticChar_exists_neg_one
    rw [ZMod.ringChar_zmod_n]
    omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [MulChar.map_zero] at hx
    norm_num at hx
  have hJ : J((x.val : ℤ) | ℓ) = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    unfold legendreSym
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hx

  set d : ℕ := x.val with hd
  set a : ℕ := (x⁻¹).val with ha
  have hdpos : 0 < d := ZMod.val_pos.2 hx0
  have hdlt : d < ℓ := ZMod.val_lt x
  have hcop : Nat.Coprime d ℓ := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdiv
    exact absurd (Nat.eq_zero_of_dvd_of_lt hdiv hdlt) hdpos.ne'
  have h1 : Int.ModEq ((ℓ * 1 : ℕ) : ℤ) ((a : ℤ) * (d : ℤ)) 1 := by
    rw [Nat.mul_one]
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ha, hd, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact inv_mul_cancel₀ hx0

  obtain ⟨z, hz⟩ := rademacher_phi_level_congruence ℓ 1 hp.one_lt.le (a : ℤ) (d : ℤ) h1
  have hodd : Odd ℓ := by
    rw [Nat.odd_iff]
    omega
  obtain ⟨t, ht⟩ := dedekindSum_jacobiSym_mod_eight d ℓ hodd hcop
  rw [hJ] at ht
  refine ⟨a, d, z, h1, hz, ?_⟩

  have hg : Nat.gcd (ℓ - 1) 12 = 12 := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero (by omega))
  rw [hg, dedekindSum_one_right, Nat.mul_one] at hz
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hzq : (ℓ : ℚ) * (12 * (z : ℚ)) = ((a : ℚ) + d) * (1 - ℓ) - (ℓ + 1 - 2 * ((-1 : ℤ) : ℚ) + 8 * t) := by
    rw [← ht]
    have e : 12 * ((((a : ℤ) + (d : ℤ) : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ : ℕ) : ℚ)) + 0
        - dedekindSum (d : ℤ) ℓ) = (((12 : ℕ) : ℕ) : ℚ) * (z : ℚ) := by exact_mod_cast hz
    push_cast at e
    field_simp at e
    linear_combination -e
  have hzi : (ℓ : ℤ) * (12 * z) = ((a : ℤ) + d) * (1 - ℓ) - (ℓ + 1 + 2 + 8 * t) := by
    have : ((((ℓ : ℤ) * (12 * z)) : ℤ) : ℚ) = ((((a : ℤ) + d) * (1 - ℓ) - (ℓ + 1 + 2 + 8 * t) : ℤ) : ℚ) := by
      push_cast
      push_cast at hzq
      linear_combination hzq
    exact_mod_cast this
  obtain ⟨q, hq⟩ : ∃ q : ℤ, (ℓ : ℤ) = 8 * q + 1 := ⟨(ℓ : ℤ) / 8, by omega⟩
  have h4 : (4 : ℤ) * (3 * z + 1 + 2 * (12 * q * z + q * ((a : ℤ) + d) + q + t)) = 0 := by
    linear_combination hzi - (12 * z + ((a : ℤ) + d) + 1) * hq
  have h3 : 3 * z + 1 + 2 * (12 * q * z + q * ((a : ℤ) + d) + q + t) = 0 := by
    have := mul_eq_zero.1 h4
    norm_num at this
    exact this
  set N : ℤ := 12 * q * z + q * ((a : ℤ) + d) + q + t with hN
  rw [Int.odd_iff]
  omega

private lemma natDvd_of_intDvd (n m : ℕ) (z : ℤ) (h : (n : ℤ) ∣ (m : ℤ) * z) : n ∣ m * z.natAbs := by
  have := Int.natAbs_dvd_natAbs.2 h
  rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at this

theorem sharpUnitNecessary_of_mod120_49 (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 120 = 49) :
    SharpUnitNecessary ℓ := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  intro m H _hm hH hpow hinv
  obtain ⟨j, hj⟩ : ∃ j, ℓ = 120 * j + 49 := ⟨ℓ / 120, by omega⟩

  obtain ⟨a, d, z, h1, hz, hzodd⟩ := exists_odd_witness ℓ (by omega) (by omega)
  have hA : (eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z :=
    ModularCurve.eisensteinNumerator_dvd_mul_of_witness ℓ hp.two_le a d 1 one_pos h1 z hz m H hH hpow hinv

  obtain ⟨hF, hcop⟩ := rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine j
  rw [← hj] at hF
  have h1' : Int.ModEq ((ℓ * 1 : ℕ) : ℤ) (((24 * j + 10 : ℕ) : ℤ) * 5) 1 :=
    modEq_helper ℓ _ _ 1 (by rw [hj]; push_cast; ring)
  have hB : (eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * (-(4 * (j : ℤ) + 2)) :=
    ModularCurve.eisensteinNumerator_dvd_mul_of_witness ℓ hp.two_le ((24 * j + 10 : ℕ) : ℤ) 5 1 one_pos h1'
      (-(4 * (j : ℤ) + 2))
      (by simpa only [Nat.mul_one, mul_one, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        Int.cast_natCast, Int.cast_one] using hF) m H hH hpow hinv

  have hn : eisensteinNumerator ℓ = 10 * j + 4 := by
    unfold eisensteinNumerator
    rw [Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero (by omega))]
    omega

  have hB' : eisensteinNumerator ℓ ∣ (m * 2) * (2 * j + 1) := by
    have := natDvd_of_intDvd _ _ _ hB
    rwa [show (-(4 * (j : ℤ) + 2)) = -((2 * (2 * j + 1) : ℕ) : ℤ) from by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast, ← mul_assoc] at this
  have hA' : eisensteinNumerator ℓ ∣ m * z.natAbs := natDvd_of_intDvd _ _ _ hA
  have hcop' : Nat.Coprime (eisensteinNumerator ℓ) (2 * j + 1) := by
    rw [hn]; exact hcop.symm
  have h2m : eisensteinNumerator ℓ ∣ m * 2 := hcop'.dvd_of_dvd_mul_right hB'
  obtain ⟨r, hr⟩ : Odd z.natAbs := Int.natAbs_odd.2 hzodd
  have hg : Nat.gcd (m * 2) (m * z.natAbs) = m := by
    rw [Nat.gcd_mul_left, hr, (coprime_two_odd r).gcd_eq_one, Nat.mul_one]
  have := Nat.dvd_gcd h2m hA'
  rwa [hg] at this

theorem sharpUnitNecessary_of_mod120_1 (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 120 = 1) :
    SharpUnitNecessary ℓ := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  intro m H _hm hH hpow hinv
  obtain ⟨j, hj⟩ : ∃ j, ℓ = 120 * j + 1 := ⟨ℓ / 120, by omega⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hp.ne_one (by omega)
  obtain ⟨w, u, ⟨t, rfl⟩, hju⟩ := Nat.exists_eq_two_pow_mul_odd hj0
  have hℓ : ℓ = 120 * 2 ^ w * (2 * t + 1) + 1 := by rw [hj, hju]; ring

  obtain ⟨a, d, z, h1, hz, hzodd⟩ := exists_odd_witness ℓ (by omega) (by omega)
  have hA : (eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z :=
    ModularCurve.eisensteinNumerator_dvd_mul_of_witness ℓ hp.two_le a d 1 one_pos h1 z hz m H hH hpow hinv

  obtain ⟨hF, hcop⟩ := rademacher_phi_level_witness_mod_oneTwenty_eq_one w t
  rw [← hℓ] at hF
  have h1' : Int.ModEq ((ℓ * 1 : ℕ) : ℤ)
      ((-((60 * 2 ^ w * (2 * t + 1) + 15 * t + 8 : ℕ) : ℤ)) * (2 ^ (w + 4))) 1 :=
    modEq_helper ℓ _ _ (-(8 * 2 ^ w + 1)) (by rw [hℓ]; push_cast; ring)
  have hB : (eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * (2 ^ (w + 1) * (5 * (t : ℤ) + 2)) :=
    ModularCurve.eisensteinNumerator_dvd_mul_of_witness ℓ hp.two_le
      (-((60 * 2 ^ w * (2 * t + 1) + 15 * t + 8 : ℕ) : ℤ)) (2 ^ (w + 4)) 1 one_pos h1'
      (2 ^ (w + 1) * (5 * (t : ℤ) + 2))
      (by simpa only [Nat.mul_one, mul_one, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        Int.cast_natCast, Int.cast_one, Int.cast_pow] using hF) m H hH hpow hinv

  have hn : eisensteinNumerator ℓ = 2 ^ (w + 1) * (5 * (2 * t + 1)) := by
    unfold eisensteinNumerator
    rw [hℓ, Nat.add_sub_cancel, show 120 * 2 ^ w * (2 * t + 1) = (10 * 2 ^ w * (2 * t + 1)) * 12 from by ring,
      Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by norm_num)]
    ring

  have hB' : 2 ^ (w + 1) * (5 * (2 * t + 1)) ∣ 2 ^ (w + 1) * (m * (5 * t + 2)) := by
    have := natDvd_of_intDvd _ _ _ hB
    rw [show (2 ^ (w + 1) * (5 * (t : ℤ) + 2)) = ((2 ^ (w + 1) * (5 * t + 2) : ℕ) : ℤ) from by push_cast; ring,
      Int.natAbs_natCast, hn] at this
    rwa [show m * (2 ^ (w + 1) * (5 * t + 2)) = 2 ^ (w + 1) * (m * (5 * t + 2)) from by ring] at this
  have hQ : 5 * (2 * t + 1) ∣ m :=
    (hcop.symm).dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_left (by positivity) hB')
  have hA' : eisensteinNumerator ℓ ∣ m * z.natAbs := natDvd_of_intDvd _ _ _ hA
  obtain ⟨r, hr⟩ : Odd z.natAbs := Int.natAbs_odd.2 hzodd
  have h2z : Nat.Coprime (2 ^ (w + 1)) z.natAbs := by
    rw [hr]; exact Nat.Coprime.pow_left _ (coprime_two_odd r)
  have hP : 2 ^ (w + 1) ∣ m := by
    refine h2z.dvd_of_dvd_mul_right ?_
    exact (Dvd.intro _ rfl : 2 ^ (w + 1) ∣ 2 ^ (w + 1) * (5 * (2 * t + 1))).trans (hn ▸ hA')
  have h2Q : Nat.Coprime (2 ^ (w + 1)) (5 * (2 * t + 1)) := by
    rw [show 5 * (2 * t + 1) = 2 * (5 * t + 2) + 1 from by ring]
    exact Nat.Coprime.pow_left _ (coprime_two_odd _)
  rw [hn]
  exact h2Q.mul_dvd_of_dvd_of_dvd hP hQ

theorem sharpUnitNecessary_of_mod_oneTwenty (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (h : ℓ % 120 = 1 ∨ ℓ % 120 = 49) : SharpUnitNecessary ℓ := by
  rcases h with h | h
  · exact sharpUnitNecessary_of_mod120_1 ℓ h
  · exact sharpUnitNecessary_of_mod120_49 ℓ h

end WN120

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (h : ℓ % 120 = 1 ∨ ℓ % 120 = 49) : ModularCurve.SharpUnitNecessary ℓ :=
  WN120.sharpUnitNecessary_of_mod_oneTwenty ℓ h

end S_ModularCurve_sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine
end P2MW
export P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine (solution)
