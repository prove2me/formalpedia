-- Prove2me | solution 1 for OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:42:11.061991+00:00
-- url     : https://prove2.me/submissions/76b08e09-f9c7-44c6-afed-973bd4e57083

import Mathlib

theorem solution
    {A : Type*} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) (hx : (p : A) ^ t ∣ algebraMap ℤ A x) :
    (p : ℤ) ^ t ∣ x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨r, s, rfl⟩ : ∃ r : ℤ, ∃ s : P.primeCompl, IsLocalization.mk' A r s = y :=
    let ⟨⟨r, s⟩, h⟩ := IsLocalization.mk'_surjective P.primeCompl y; ⟨r, s, h⟩
  have hs : ∀ c : P.primeCompl, ¬ (p : ℤ) ∣ (c : ℤ) := by
    intro c hc
    apply c.2
    have : (c : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := Ideal.mem_span_singleton.2 hc
    rw [← hP] at this; exact this
  have h1 : algebraMap ℤ A (x * s) = algebraMap ℤ A ((p : ℤ) ^ t * r) := by
    rw [map_mul, hy, map_mul, map_pow, map_natCast, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl A).1 h1
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hcop : IsCoprime ((p : ℤ) ^ t) ((c : ℤ) * s) := by
    apply IsCoprime.pow_left
    rw [Prime.coprime_iff_not_dvd hpr]
    intro h
    rcases hpr.dvd_or_dvd h with h | h
    · exact hs c h
    · exact hs s h
  have : (p : ℤ) ^ t ∣ x * ((c : ℤ) * s) := ⟨c * r, by linear_combination hc⟩
  exact hcop.dvd_of_dvd_mul_right this
