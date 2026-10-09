-- Prove2me | solution 1 for Helfgott.moebius_initial_integral_of_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:19:17.458649+00:00
-- url     : https://prove2.me/submissions/51de1fc5-7c4a-452e-8413-df9830cf9f11

import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
namespace Helfgott

-- A proper small divisor disqualifies every composite; only the prime cases need membership.
def mobiusSmallPrimeCompletenessCheck : Bool :=
  (List.range 1101).all (fun n =>
    decide (n < 2) ||
      ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).any
        (fun d => decide (2 ≤ d) && decide (d < n) && (n % d == 0)) ||
      decide (n ∈ mobiusSmallPrimes))

lemma mobiusSmallPrimeCompletenessCheck_checked :
    mobiusSmallPrimeCompletenessCheck = true := by decide +kernel

lemma mobiusSmallPrimes_complete_fast :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes := by
  intro p hp
  have hc := List.all_eq_true.mp mobiusSmallPrimeCompletenessCheck_checked
    p.val (by simpa using p.isLt)
  have fields : p.val < 2 ∨
      (∃ d ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ),
        2 ≤ d ∧ d < p.val ∧ p.val % d = 0) ∨ p.val ∈ mobiusSmallPrimes := by
    simpa [mobiusSmallPrimeCompletenessCheck, List.any_eq_true, Bool.or_assoc, or_assoc,
      Bool.and_assoc, and_assoc] using hc
  rcases fields with hsmall | hdiv | hmem
  · have hp2 := hp.two_le
    omega
  · obtain ⟨d, hdL, hd2, hdp, hdmod⟩ := hdiv
    exact False.elim ((Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hdmod) hd2 hdp) hp)
  · exact hmem

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

lemma mobiusSmallPrimes_sound : ∀ p ∈ mobiusSmallPrimes, Nat.Prime p := by
  simp only [mobiusSmallPrimes, List.forall_mem_cons]
  exact ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

lemma mobiusSmallPrimes_complete :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes :=
  mobiusSmallPrimes_complete_fast

lemma mobiusSmallPrimeCheck_sound (n : ℕ) (hn : n < 1200001)
    (hc : mobiusSmallPrimeCheck n = true) : Nat.Prime n := by
  have hcfields : 2 ≤ n ∧ mobiusSmallPrimes.all (fun p =>
      if p * p ≤ n then !(n % p == 0) else true) = true := by
    simpa [mobiusSmallPrimeCheck] using hc
  have hn2 : 2 ≤ n := hcfields.1
  by_contra hnot
  let p := n.minFac
  have hpp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hpsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnot
  have hpbound : p < 1101 := by nlinarith
  have hmem : p ∈ mobiusSmallPrimes := mobiusSmallPrimes_complete ⟨p, hpbound⟩ hpp
  have hall : mobiusSmallPrimes.all (fun p =>
      if p * p ≤ n then !(n % p == 0) else true) = true :=
    hcfields.2
  have hpcheck := List.all_eq_true.mp hall p hmem
  have hdiv : n % p = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
  simp [show p * p ≤ n by simpa [pow_two] using hpsq, hdiv] at hpcheck

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

theorem moebius_of_local_checks (g : ℕ → ℤ) (B : ℕ) (hB : B ≤ 1200001)
    (hc : ∀ n < B, ∃ p, mobiusLocalCheck g n p = true) :
    ∀ n < B, g n = moebius n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnB
    obtain ⟨p, hpcheck⟩ := hc n hnB
    by_cases hn0 : n = 0
    · subst n
      simpa [mobiusLocalCheck] using hpcheck
    by_cases hn1 : n = 1
    · subst n
      simpa [mobiusLocalCheck] using hpcheck
    by_cases hp0 : p = 0
    · subst p
      have hh : mobiusSmallPrimeCheck n = true ∧ g n = -1 := by
        simpa [mobiusLocalCheck, hn0, hn1] using hpcheck
      have hp := mobiusSmallPrimeCheck_sound n (lt_of_lt_of_le hnB hB) hh.1
      rw [hh.2, moebius_apply_prime hp]
    have hfields : p ∈ mobiusSmallPrimes ∧ p < n ∧ n % p = 0 ∧
        g n = (if (n / p) % p == 0 then 0 else -g (n / p)) := by
      simpa [mobiusLocalCheck, hn0, hn1, hp0, Bool.and_assoc, and_assoc] using hpcheck
    obtain ⟨hpL, hpn, hdiv, hvalue⟩ := hfields
    have hpp := mobiusSmallPrimes_sound p hpL
    have hnp : p ∣ n := Nat.dvd_of_mod_eq_zero hdiv
    have hprod : p * (n / p) = n := Nat.mul_div_cancel' hnp
    have hp2 : 2 ≤ p := hpp.two_le
    have hquot : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
    have hrec := ih (n / p) hquot (lt_trans hquot hnB)
    by_cases hq : (n / p) % p = 0
    · have hpsq : p ^ 2 ∣ n := by
        rw [← hprod, pow_two]
        exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mod_eq_zero hq)
      have hnsq : ¬Squarefree n := by
        intro hs
        have hp2 := hs.squarefree_of_dvd hpsq
        have hf := (Nat.squarefree_pow_iff hpp.ne_one (by norm_num : (2 : ℕ) ≠ 0)).mp hp2
        norm_num at hf
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simpa [hq] using hvalue
    · have hcop : Nat.Coprime p (n / p) := hpp.coprime_iff_not_dvd.mpr
        (fun hd => hq (Nat.mod_eq_zero_of_dvd hd))
      rw [← hprod, isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hpp]
      simpa [hprod, hq, hrec] using hvalue

lemma mobiusTreeCheck_local_sound (g : ℕ → ℤ) (B d offset : ℕ) (tree : MobiusCertTree)
    (hc : mobiusTreeCheck g B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → n < B →
      ∃ p, mobiusLocalCheck g n p = true := by
  induction d generalizing offset tree with
  | zero =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf muDigits factorDigits =>
      have hh : mobiusLeafCheck g B offset factorDigits = true := by
        simpa [mobiusTreeCheck, hoff] using hc
      have hk : n - offset ∈ List.range 32 := by
        simp only [List.mem_range]
        simp only [pow_zero, mul_one] at hup
        omega
      have hlocal := List.all_eq_true.mp hh (n - offset) hk
      have he : offset + (n - offset) = n := Nat.add_sub_of_le hlo
      simp only [mobiusLeafCheck] at hh
      rw [he, if_pos hnB] at hlocal
      exact ⟨_, hlocal⟩
    | branch l r => simp [mobiusTreeCheck, hoff] at hc
  | succ d ih =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf muDigits factorDigits => simp [mobiusTreeCheck, hoff] at hc
    | branch l r =>
      have hh : mobiusTreeCheck g B d offset l = true ∧
          mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true := by
        simpa [mobiusTreeCheck, hoff] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan] at hup
      by_cases hsplit : n < offset + 32 * 2 ^ d
      · exact ih offset l hh.1 n hlo hsplit hnB
      · exact ih (offset + 32 * 2 ^ d) r hh.2 n (by omega) (by omega) hnB

theorem mobiusTreeCheck_sound (B d : ℕ) (tree : MobiusCertTree)
    (hB : B ≤ 1200001) (hcapacity : B ≤ 32 * 2 ^ d)
    (hc : mobiusTreeCheck (mobiusTreeValue d tree) B d 0 tree = true) :
    ∀ n < B, mobiusTreeValue d tree n = moebius n := by
  apply moebius_of_local_checks _ B hB
  intro n hn
  exact mobiusTreeCheck_local_sound _ B d 0 tree hc n (Nat.zero_le n)
    (by simpa using lt_of_lt_of_le hn hcapacity) hn

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma mobiusHarmonicCeil_bound (Q n : ℕ) (s : ℤ) (hQ : 0 < Q) :
    |(s : ℝ)| / (n : ℝ) ≤ (mobiusHarmonicCeil Q n s : ℝ) / (Q : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, mobiusHarmonicCeil]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hmod := Nat.mod_lt (s.natAbs * Q + n - 1) hnpos
  have hdiv := Nat.div_add_mod (s.natAbs * Q + n - 1) n
  rw [Nat.mul_comm n ((s.natAbs * Q + n - 1) / n)] at hdiv
  have hmul : s.natAbs * Q ≤ ((s.natAbs * Q + n - 1) / n) * n := by
    omega
  have hcast : |(s : ℝ)| * (Q : ℝ) ≤
      (((s.natAbs * Q + n - 1) / n : ℕ) : ℝ) * (n : ℝ) := by
    have hcast0 : (s.natAbs : ℝ) * (Q : ℝ) ≤
        (((s.natAbs * Q + n - 1) / n : ℕ) : ℝ) * (n : ℝ) := by
      exact_mod_cast hmul
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [mobiusHarmonicCeil, if_neg hn]
  exact (div_le_div_iff₀ hnR hQR).mpr hcast

lemma prefix_of_local_checks (g M : ℕ → ℤ) (B : ℕ)
    (hc : ∀ n < B, mobiusPrefixLocalCheck g M n = true) :
    ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hh := hc 0 hn
    simpa [mobiusPrefixLocalCheck] using hh
  | succ n ih =>
    intro hn
    have hh := hc (n + 1) hn
    have hs : M (n + 1) = M n + g (n + 1) := by
      simpa [mobiusPrefixLocalCheck] using hh
    rw [hs, ih (by omega), Finset.sum_range_succ (f := g) (n := n + 1)]

lemma mobiusHarmonicTreeCheck_local_sound (g M : ℕ → ℤ) (Q B d offset : ℕ)
    (tree : MobiusHarmonicTree)
    (hc : mobiusHarmonicTreeCheck g M Q B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → n < B →
      mobiusPrefixLocalCheck g M n = true := by
  induction d generalizing offset tree with
  | zero =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf digits upper =>
      have hh : mobiusHarmonicLeafCheck g M Q B offset upper = true := by
        simpa [mobiusHarmonicTreeCheck, hoff] using hc
      have hall : (List.range 32).all (fun k =>
          if offset + k < B then mobiusPrefixLocalCheck g M (offset + k) else true) = true :=
        (Bool.and_eq_true_iff.mp hh).1
      have hk : n - offset ∈ List.range 32 := by
        simp only [List.mem_range]
        simp only [pow_zero, mul_one] at hup
        omega
      have hlocal := List.all_eq_true.mp hall (n - offset) hk
      have he : offset + (n - offset) = n := Nat.add_sub_of_le hlo
      rwa [he, if_pos hnB] at hlocal
    | branch upper l r => simp [mobiusHarmonicTreeCheck, hoff] at hc
  | succ d ih =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf digits upper => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | branch upper l r =>
      have hh : mobiusHarmonicTreeCheck g M Q B d offset l = true ∧
          mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true ∧
          upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r := by
        simpa [mobiusHarmonicTreeCheck, hoff, Bool.and_assoc, and_assoc] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan] at hup
      by_cases hsplit : n < offset + 32 * 2 ^ d
      · exact ih offset l hh.1 n hlo hsplit hnB
      · exact ih (offset + 32 * 2 ^ d) r hh.2.1 n (by omega) (by omega) hnB

lemma mobiusHarmonicTreeCheck_bound (g M : ℕ → ℤ) (Q B d offset : ℕ)
    (tree : MobiusHarmonicTree) (hQ : 0 < Q)
    (hc : mobiusHarmonicTreeCheck g M Q B d offset tree = true) :
    (∑ k ∈ Finset.range (32 * 2 ^ d),
      if offset + k < B then |(M (offset + k) : ℝ)| / (offset + k : ℕ) else 0) ≤
      (mobiusHarmonicUpper tree : ℝ) / (Q : ℝ) := by
  induction d generalizing offset tree with
  | zero =>
    by_cases hoff : B ≤ offset
    · have hu : mobiusHarmonicUpper tree = 0 := by
        cases tree <;> simpa [mobiusHarmonicTreeCheck, hoff, mobiusHarmonicUpper] using hc
      rw [hu]
      apply le_of_eq
      simp only [Nat.cast_zero, zero_div]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by omega)]
    cases tree with
    | branch upper l r => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | leaf digits upper =>
      have hh : mobiusHarmonicLeafCheck g M Q B offset upper = true := by
        simpa [mobiusHarmonicTreeCheck, hoff] using hc
      have huL : ((List.range 32).map (fun k =>
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0)).sum = upper := by
        simpa using (Bool.and_eq_true_iff.mp hh).2
      have hu : (∑ k ∈ Finset.range 32,
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0) = upper := by
        rw [← huL]
        have hset : (List.range 32).toFinset = Finset.range 32 := by
          ext k
          simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
        simpa only [hset] using List.sum_toFinset (fun k =>
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0) (List.nodup_range (n := 32))
      have huR : (∑ k ∈ Finset.range 32,
          if offset + k < B then (mobiusHarmonicCeil Q (offset + k) (M (offset + k)) : ℝ)
          else 0) = (upper : ℝ) := by exact_mod_cast hu
      simp only [pow_zero, mul_one, mobiusHarmonicUpper]
      calc
        _ ≤ (∑ k ∈ Finset.range 32,
            if offset + k < B then
              (mobiusHarmonicCeil Q (offset + k) (M (offset + k)) : ℝ) else 0) / (Q : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_le_sum
          intro k hk
          by_cases hkB : offset + k < B
          · simp only [if_pos hkB]
            exact mobiusHarmonicCeil_bound Q (offset + k) (M (offset + k)) hQ
          · simp [hkB]
        _ = _ := by rw [huR]
  | succ d ih =>
    by_cases hoff : B ≤ offset
    · have hu : mobiusHarmonicUpper tree = 0 := by
        cases tree <;> simpa [mobiusHarmonicTreeCheck, hoff, mobiusHarmonicUpper] using hc
      rw [hu]
      apply le_of_eq
      simp only [Nat.cast_zero, zero_div]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by omega)]
    cases tree with
    | leaf digits upper => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | branch upper l r =>
      have hh : mobiusHarmonicTreeCheck g M Q B d offset l = true ∧
          mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true ∧
          upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r := by
        simpa [mobiusHarmonicTreeCheck, hoff, Bool.and_assoc, and_assoc] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan, Finset.sum_range_add]
      have hl := ih offset l hh.1
      have hr := ih (offset + 32 * 2 ^ d) r hh.2.1
      have hr' : (∑ k ∈ Finset.range (32 * 2 ^ d),
          if offset + (32 * 2 ^ d + k) < B then
            |(M (offset + (32 * 2 ^ d + k)) : ℝ)| / (offset + (32 * 2 ^ d + k) : ℕ)
          else 0) ≤ (mobiusHarmonicUpper r : ℝ) / (Q : ℝ) := by
        simpa [Nat.add_assoc] using hr
      calc
        _ ≤ (mobiusHarmonicUpper l : ℝ) / (Q : ℝ) +
            (mobiusHarmonicUpper r : ℝ) / (Q : ℝ) := add_le_add hl hr'
        _ = _ := by simp only [mobiusHarmonicUpper, hh.2.2, Nat.cast_add, add_div]

theorem moebius_finite_harmonic_certificate (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∑ n ∈ Finset.Ico 1 B,
      |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| / (n : ℝ)) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) := by
  let g := mobiusTreeValue dm muTree
  let M := mobiusPrefixValue dh hTree
  have hg : ∀ n < B, g n = moebius n := mobiusTreeCheck_sound B dm muTree hB hmCapacity hm
  have hp : ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
    apply prefix_of_local_checks g M B
    intro n hn
    exact mobiusHarmonicTreeCheck_local_sound g M Q B dh 0 hTree hh n (Nat.zero_le _)
      (by simpa using lt_of_lt_of_le hn hhCapacity) hn
  have hM (n : ℕ) (hn : n < B) :
      (M n : ℝ) = ∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ) := by
    have ht : M n = ∑ d ∈ Finset.range (n + 1), moebius d := by
      rw [hp n hn]
      apply Finset.sum_congr rfl
      intro d hd
      exact hg d (by have h := Finset.mem_range.mp hd; omega)
    rw [Finset.sum_range_eq_add_Ico (fun d => moebius d) (Nat.zero_lt_succ n),
      ArithmeticFunction.map_zero, zero_add] at ht
    simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at ht
    exact_mod_cast ht
  have hb := mobiusHarmonicTreeCheck_bound g M Q B dh 0 hTree hQ hh
  simp only [zero_add] at hb
  have heq : (∑ n ∈ Finset.range (32 * 2 ^ dh),
      if n < B then |(M n : ℝ)| / (n : ℝ) else 0) =
      ∑ n ∈ Finset.range B, |(M n : ℝ)| / (n : ℝ) := by
    symm
    calc
      _ = ∑ n ∈ Finset.range B, if n < B then |(M n : ℝ)| / (n : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (Finset.mem_range.mp hn)]
      _ = _ := Finset.sum_subset (Finset.range_mono hhCapacity) (by
        intro n hn hnB
        rw [if_neg (by simpa only [Finset.mem_range] using hnB)])
  rw [heq] at hb
  calc
    _ = ∑ n ∈ Finset.Ico 1 B, |(M n : ℝ)| / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hM n (Finset.mem_Ico.mp hn).2]
    _ = ∑ n ∈ Finset.range B, |(M n : ℝ)| / (n : ℝ) := by
      apply Finset.sum_subset (by intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at *; omega)
      intro n hn hnI
      have hnB := Finset.mem_range.mp hn
      have hn0 : n = 0 := by simp only [Finset.mem_Ico] at hnI; omega
      simp [hn0]
    _ ≤ _ := hb

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma moebius_abs_summatory_single_interval (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (n : ℝ)..(n + 1 : ℕ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
      |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
        Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsucc : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    _ = ∫ t in (n : ℝ)..(n + 1 : ℕ),
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| * t⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by exact_mod_cast Nat.le_succ n)
      intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff ht0).mpr ⟨ht.1.le, by
        exact_mod_cast ht.2⟩
      dsimp only
      rw [hf]
      simp only [div_eq_mul_inv]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hnp hsucc]

theorem moebius_finite_initial_integral_certificate (B : ℕ) (hB : 1 ≤ B) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
      (∑ n ∈ Finset.Ico 1 B,
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
          Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) ∧
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      ∑ n ∈ Finset.Ico 1 B,
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| / (n : ℝ) := by
  have hi (n : ℕ) (hn : n ∈ Finset.Ico 1 B) :
      IntervalIntegrable (fun t : ℝ =>
        |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t)
        volume (n : ℝ) (n + 1 : ℕ) := by
    have hn1 := (Finset.mem_Ico.mp hn).1
    have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    have hb : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (n : ℝ) (n + 1 : ℕ) := by
      apply intervalIntegral.intervalIntegrable_inv (f := fun t : ℝ => t)
      · intro t ht
        simp only [Set.uIcc_of_le hle, Set.mem_Icc] at ht
        exact (hnp.trans_le ht.1).ne'
      · exact continuous_id.continuousOn
    apply (hb.const_mul |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)|).congr_uIoo
    intro t ht
    simp only [Set.uIoo_of_le hle, Set.mem_Ioo] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff ht0).mpr ⟨ht.1.le, by exact_mod_cast ht.2⟩
    dsimp only
    rw [hf]
    simp only [div_eq_mul_inv]
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n : ℝ))
    hB (fun n hn => hi n (Finset.mem_Ico.mpr hn))
  simp only [Nat.cast_one] at hs
  have hid :
      (∫ t in (1 : ℝ)..(B : ℝ),
        |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
        ∑ n ∈ Finset.Ico 1 B,
          |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
            Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro n hn
    exact moebius_abs_summatory_single_interval n (Finset.mem_Ico.mp hn).1
  refine ⟨hid, ?_⟩
  rw [hid]
  apply Finset.sum_le_sum
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by have h := (Finset.mem_Ico.mp hn).1; omega : 0 < n)
  have hsucc : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hnp)
  calc
    _ ≤ |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
        (((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ = _ := by push_cast; field_simp; ring

end Helfgott
end

section
set_option autoImplicit false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_initial_integral_of_finite_certificate_complete (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hBpos : 1 ≤ B) (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) :=
  (moebius_finite_initial_integral_certificate B hBpos).2.trans
    (moebius_finite_harmonic_certificate B dm dh Q muTree hTree hB hmCapacity hhCapacity hQ hm hh)

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

theorem solution  (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hBpos : 1 ≤ B) (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) := Helfgott.moebius_initial_integral_of_finite_certificate_complete B dm dh Q muTree hTree hBpos hB hmCapacity hhCapacity hQ hm hh

#print axioms solution
