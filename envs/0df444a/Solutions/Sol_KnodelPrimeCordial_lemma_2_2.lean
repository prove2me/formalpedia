-- Prove2me | solution 1 for KnodelPrimeCordial.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T15:14:49.818476+00:00
-- url     : https://prove2.me/submissions/9a6c23dd-01d1-445d-a963-82a8fe552f60

import Mathlib

set_option autoImplicit false

/-- `x` and `y` are coprime iff no prime dividing `|x - y|` divides `x`. -/
theorem solution (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    Nat.Coprime x y ↔ ∀ p ∈ (Int.natAbs ((x : ℤ) - (y : ℤ))).primeFactors, x % p ≠ 0 := by
  constructor
  · intro hcop p hp hmod
    have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hpdiv : p ∣ Int.natAbs ((x : ℤ) - (y : ℤ)) := (Nat.mem_primeFactors.mp hp).2.1
    have hpx : p ∣ x := Nat.dvd_of_mod_eq_zero hmod
    have hpdiff : (p : ℤ) ∣ ((x : ℤ) - (y : ℤ)) := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast hpdiv
    have hpxz : (p : ℤ) ∣ (x : ℤ) := by exact_mod_cast hpx
    have hpyz : (p : ℤ) ∣ (y : ℤ) := by
      have h := Int.dvd_sub hpxz hpdiff
      simpa using h
    have hpy : p ∣ y := by exact_mod_cast hpyz
    have hpgcd : p ∣ Nat.gcd x y := Nat.dvd_gcd hpx hpy
    have hgcd1 : Nat.gcd x y = 1 := by simpa [Nat.Coprime] using hcop
    rw [hgcd1] at hpgcd
    exact hpprime.not_dvd_one hpgcd
  · intro h
    by_contra hnc
    have hgcd_ne : Nat.gcd x y ≠ 1 := by simpa [Nat.Coprime] using hnc
    have hgcd_pos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left y hx
    have hgcd_gt : 1 < Nat.gcd x y := by omega
    obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd hgcd_ne
    have hpx : p ∣ x := hpdiv.trans (Nat.gcd_dvd_left x y)
    have hpy : p ∣ y := hpdiv.trans (Nat.gcd_dvd_right x y)
    have hpdiffz : (p : ℤ) ∣ ((x : ℤ) - (y : ℤ)) := by
      have hpxz : (p : ℤ) ∣ (x : ℤ) := by exact_mod_cast hpx
      have hpyz : (p : ℤ) ∣ (y : ℤ) := by exact_mod_cast hpy
      exact Int.dvd_sub hpxz hpyz
    have hpdiv_abs : p ∣ Int.natAbs ((x : ℤ) - (y : ℤ)) := by
      have hz : (p : ℤ) ∣ ((x : ℤ) - (y : ℤ)).natAbs := by
        rw [Int.dvd_natAbs]
        exact hpdiffz
      exact_mod_cast hz
    have hne : Int.natAbs ((x : ℤ) - (y : ℤ)) ≠ 0 := by
      intro hzero
      apply hxy
      have hz : (x : ℤ) - (y : ℤ) = 0 := Int.natAbs_eq_zero.mp hzero
      have hzy : (x : ℤ) = (y : ℤ) := sub_eq_zero.mp hz
      exact_mod_cast hzy
    have hmem : p ∈ (Int.natAbs ((x : ℤ) - (y : ℤ))).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, hpdiv_abs, hne⟩
    have hmod : x % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpx
    exact h p hmem hmod
