-- Prove2me | solution 1 for N25.characterField_prime_norm_small
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:46.914693+00:00
-- url     : https://prove2.me/submissions/565c6c2c-4496-480b-b7fe-2c50ab08563e

import Mathlib
import Theorems.Thm_N25_characterField_prime_norm_residue
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic
import Theorems.Thm_N25_characterField_degree_and_totallyReal
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open scoped NumberField

namespace N25

private theorem prime_power_not_divisible_two_three (n p k : ℕ)
    (hp : Nat.Prime p) (hn : n = p ^ k) (h2 : 2 ∣ n) (h3 : 3 ∣ n) : False := by
  rw [hn] at h2 h3
  have hp2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2
  have hp3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h3
  have he2 : 2 = p := ((Nat.dvd_prime hp).mp hp2).resolve_left (by decide)
  have he3 : 3 = p := ((Nat.dvd_prime hp).mp hp3).resolve_left (by decide)
  omega

/-- The only prime ideal norms at most 24 in the literal quintic field
are 5 and 7. -/
theorem _root_.solution (P : Ideal (𝓞 characterField))
    [P.IsPrime] (hP : P ≠ ⊥) (hbound : P.absNorm ≤ 24) :
    P.absNorm = 5 ∨ P.absNorm = 7 := by
  haveI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  obtain ⟨p, k, hk, hpmem, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  by_cases h5 : (5 : 𝓞 characterField) ∈ P
  · have hd : (P.absNorm : ℤ) ∣ Algebra.norm ℤ (5 : 𝓞 characterField) :=
      Ideal.absNorm_dvd_norm_of_mem h5
    have hdeg : Module.finrank ℚ characterField = 5 :=
      characterField_degree_and_totallyReal.1
    have hnormfive : Algebra.norm ℤ (5 : 𝓞 characterField) = (5 : ℤ) ^ 5 := by
      rw [show (5 : 𝓞 characterField) = algebraMap ℤ _ 5 by simp,
        Algebra.norm_algebraMap]
      have hr : Module.finrank ℤ (𝓞 characterField) = 5 := by
        rw [NumberField.RingOfIntegers.rank] 
        exact hdeg
      rw [hr]
    rw [hnormfive] at hd
    have hdN : P.absNorm ∣ 5 ^ 5 := by exact_mod_cast hd
    have hp5 : p ∣ 5 := hp.dvd_of_dvd_pow ((dvd_pow_self p hk.ne').trans (hnorm ▸ hdN))
    have hep : p = 5 := ((Nat.dvd_prime Nat.prime_five).mp hp5).resolve_left hp.ne_one
    subst p
    have hk1 : k = 1 := by
      have hlt : k < 2 := by
        by_contra! hge
        have hh : 5 ^ 2 ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) hge
        omega
      omega
    left
    simpa [hk1] using hnorm
  · obtain ⟨Q, hQmax, hQP⟩ :=
      Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 cyclotomicField) P (by simp)
    letI : Q.IsMaximal := hQmax
    have hunder : Q.under (𝓞 characterField) = P := hQP
    have hQzero : Q ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int Q
    haveI : Finite ((𝓞 cyclotomicField) ⧸ Q) :=
      (Ideal.absNorm_ne_zero_iff Q).mp (mt Ideal.absNorm_eq_zero_iff.mp hQzero)
    have h25 : (25 : 𝓞 cyclotomicField) ∉ Q := by
      intro h25
      have h5Q : (5 : 𝓞 cyclotomicField) ∈ Q :=
        (Ideal.IsPrime.pow_mem_iff_mem inferInstance _ (by decide : 0 < 2)).mp (by norm_num at h25 ⊢; exact h25)
      apply h5
      rw [← hunder]
      change algebraMap (𝓞 characterField) (𝓞 cyclotomicField) 5 ∈ Q
      simpa only [map_ofNat] using h5Q
    have hres := characterField_prime_norm_residue Q h25 (by simpa only [hunder] using hbound)
    rw [hunder] at hres
    have hcast (r : ℕ) (hr : r < 25) (h : (P.absNorm : ZMod 25) = (r : ZMod 25)) :
        P.absNorm = r := by
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : P.absNorm < 25),
        Nat.mod_eq_of_lt hr] using hv
    rcases hres with h | h | h | h
    · have hn1 := hcast 1 (by decide) h
      exact False.elim ((inferInstance : P.IsPrime).ne_top (Ideal.absNorm_eq_one_iff.mp hn1))
    · exact Or.inr (hcast 7 (by decide) h)
    · have hn18 := hcast 18 (by decide) h
      exact False.elim (prime_power_not_divisible_two_three P.absNorm p k hp hnorm
        (by omega) (by omega))
    · have hn24 := hcast 24 (by decide) h
      exact False.elim (prime_power_not_divisible_two_three P.absNorm p k hp hnorm
        (by omega) (by omega))

end N25
