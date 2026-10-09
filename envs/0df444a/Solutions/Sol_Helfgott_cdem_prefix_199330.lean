-- Prove2me | solution 1 for Helfgott.cdem_prefix_199330
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T03:11:39.327986+00:00
-- url     : https://prove2.me/submissions/d7e274a5-d39d-4f04-ba1e-5f58c48ac6c7

import Theorems.Thm_Helfgott_cdemPrefixGroup000_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup001_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup002_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup003_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup004_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup005_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup006_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup007_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup008_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup009_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup010_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup011_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup012_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup013_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup014_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup015_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup016_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup017_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup018_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup019_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup020_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup021_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup022_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup023_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup024_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup025_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup026_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup027_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup028_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup029_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup030_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup031_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup032_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup033_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup034_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup035_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup036_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup037_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup038_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup039_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup040_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup041_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup042_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup043_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup044_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup045_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup046_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup047_checked
import Theorems.Thm_Helfgott_cdemPrefixGroup048_checked
import Theorems.Thm_Helfgott_mobiusValuePair000_checked
import Theorems.Thm_Helfgott_mobiusValuePair001_checked
import Theorems.Thm_Helfgott_mobiusValuePair002_checked
import Theorems.Thm_Helfgott_mobiusValuePair003_checked
import Theorems.Thm_Helfgott_mobiusValuePair004_checked
import Theorems.Thm_Helfgott_mobiusValuePair005_checked
import Theorems.Thm_Helfgott_mobiusValuePair006_checked
import Theorems.Thm_Helfgott_mobiusValuePair007_checked
import Theorems.Thm_Helfgott_mobiusValuePair008_checked
import Theorems.Thm_Helfgott_mobiusValuePair009_checked
import Theorems.Thm_Helfgott_mobiusValuePair010_checked
import Theorems.Thm_Helfgott_mobiusValuePair011_checked
import Theorems.Thm_Helfgott_mobiusValuePair012_checked
import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.SpecialFunctions.Sqrt

section
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
namespace Helfgott

-- A proper small divisor disqualifies every composite; only the prime cases need membership.
def cdem_prefix_assembled_mobiusSmallPrimeCompletenessCheck : Bool :=
  (List.range 1101).all (fun n =>
    decide (n < 2) ||
      ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).any
        (fun d => decide (2 ≤ d) && decide (d < n) && (n % d == 0)) ||
      decide (n ∈ mobiusSmallPrimes))

lemma cdem_prefix_assembled_mobiusSmallPrimeCompletenessCheck_checked :
    cdem_prefix_assembled_mobiusSmallPrimeCompletenessCheck = true := by decide +kernel

lemma cdem_prefix_assembled_mobiusSmallPrimes_complete_fast :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes := by
  intro p hp
  have hc := List.all_eq_true.mp cdem_prefix_assembled_mobiusSmallPrimeCompletenessCheck_checked
    p.val (by simpa using p.isLt)
  have fields : p.val < 2 ∨
      (∃ d ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ),
        2 ≤ d ∧ d < p.val ∧ p.val % d = 0) ∨ p.val ∈ mobiusSmallPrimes := by
    simpa [cdem_prefix_assembled_mobiusSmallPrimeCompletenessCheck, List.any_eq_true, Bool.or_assoc, or_assoc,
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

lemma cdem_prefix_assembled_mobiusSmallPrimes_sound : ∀ p ∈ mobiusSmallPrimes, Nat.Prime p := by
  simp only [mobiusSmallPrimes, List.forall_mem_cons]
  exact ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

lemma cdem_prefix_assembled_mobiusSmallPrimes_complete :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes :=
  cdem_prefix_assembled_mobiusSmallPrimes_complete_fast

lemma cdem_prefix_assembled_mobiusSmallPrimeCheck_sound (n : ℕ) (hn : n < 1200001)
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
  have hmem : p ∈ mobiusSmallPrimes := cdem_prefix_assembled_mobiusSmallPrimes_complete ⟨p, hpbound⟩ hpp
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

theorem cdem_prefix_assembled_moebius_of_local_checks (g : ℕ → ℤ) (B : ℕ) (hB : B ≤ 1200001)
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
      have hp := cdem_prefix_assembled_mobiusSmallPrimeCheck_sound n (lt_of_lt_of_le hnB hB) hh.1
      rw [hh.2, moebius_apply_prime hp]
    have hfields : p ∈ mobiusSmallPrimes ∧ p < n ∧ n % p = 0 ∧
        g n = (if (n / p) % p == 0 then 0 else -g (n / p)) := by
      simpa [mobiusLocalCheck, hn0, hn1, hp0, Bool.and_assoc, and_assoc] using hpcheck
    obtain ⟨hpL, hpn, hdiv, hvalue⟩ := hfields
    have hpp := cdem_prefix_assembled_mobiusSmallPrimes_sound p hpL
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

lemma cdem_prefix_assembled_mobiusTreeCheck_local_sound (g : ℕ → ℤ) (B d offset : ℕ) (tree : MobiusCertTree)
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

theorem cdem_prefix_assembled_mobiusTreeCheck_sound (B d : ℕ) (tree : MobiusCertTree)
    (hB : B ≤ 1200001) (hcapacity : B ≤ 32 * 2 ^ d)
    (hc : mobiusTreeCheck (mobiusTreeValue d tree) B d 0 tree = true) :
    ∀ n < B, mobiusTreeValue d tree n = moebius n := by
  apply cdem_prefix_assembled_moebius_of_local_checks _ B hB
  intro n hn
  exact cdem_prefix_assembled_mobiusTreeCheck_local_sound _ B d 0 tree hc n (Nat.zero_le n)
    (by simpa using lt_of_lt_of_le hn hcapacity) hn

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma cdem_prefix_assembled_mobiusHarmonicCeil_bound (Q n : ℕ) (s : ℤ) (hQ : 0 < Q) :
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

lemma cdem_prefix_assembled_prefix_of_local_checks (g M : ℕ → ℤ) (B : ℕ)
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

lemma cdem_prefix_assembled_mobiusHarmonicTreeCheck_local_sound (g M : ℕ → ℤ) (Q B d offset : ℕ)
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

lemma cdem_prefix_assembled_mobiusHarmonicTreeCheck_bound (g M : ℕ → ℤ) (Q B d offset : ℕ)
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
            exact cdem_prefix_assembled_mobiusHarmonicCeil_bound Q (offset + k) (M (offset + k)) hQ
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

theorem cdem_prefix_assembled_moebius_finite_harmonic_certificate (B dm dh Q : ℕ)
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
  have hg : ∀ n < B, g n = moebius n := cdem_prefix_assembled_mobiusTreeCheck_sound B dm muTree hB hmCapacity hm
  have hp : ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
    apply cdem_prefix_assembled_prefix_of_local_checks g M B
    intro n hn
    exact cdem_prefix_assembled_mobiusHarmonicTreeCheck_local_sound g M Q B dh 0 hTree hh n (Nat.zero_le _)
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
  have hb := cdem_prefix_assembled_mobiusHarmonicTreeCheck_bound g M Q B dh 0 hTree hQ hh
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

lemma cdem_prefix_assembled_moebius_abs_summatory_single_interval (n : ℕ) (hn : 1 ≤ n) :
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

theorem cdem_prefix_assembled_moebius_finite_initial_integral_certificate (B : ℕ) (hB : 1 ≤ B) :
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
    exact cdem_prefix_assembled_moebius_abs_summatory_single_interval n (Finset.mem_Ico.mp hn).1
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

theorem cdem_prefix_assembled_moebius_initial_integral_of_finite_certificate_complete (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hBpos : 1 ≤ B) (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) :=
  (cdem_prefix_assembled_moebius_finite_initial_integral_certificate B hBpos).2.trans
    (cdem_prefix_assembled_moebius_finite_harmonic_certificate B dm dh Q muTree hTree hB hmCapacity hhCapacity hQ hm hh)

end Helfgott
end
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction Finset
open scoped BigOperators Classical
namespace Helfgott
abbrev cdem_prefix_assembled_cdemCandidateMu : ℕ → ℤ := mobiusTreeValue 16 mobiusTable1200001

lemma cdem_prefix_assembled_cdemPair000 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 0 (.branch mobiusTableBlock000 mobiusTableBlock001) = true := mobiusValuePair000_checked

lemma cdem_prefix_assembled_cdemPair001 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 16384 (.branch mobiusTableBlock002 mobiusTableBlock003) = true := mobiusValuePair001_checked

lemma cdem_prefix_assembled_cdemPair002 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 32768 (.branch mobiusTableBlock004 mobiusTableBlock005) = true := mobiusValuePair002_checked

lemma cdem_prefix_assembled_cdemPair003 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 49152 (.branch mobiusTableBlock006 mobiusTableBlock007) = true := mobiusValuePair003_checked

lemma cdem_prefix_assembled_cdemPair004 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 65536 (.branch mobiusTableBlock008 mobiusTableBlock009) = true := mobiusValuePair004_checked

lemma cdem_prefix_assembled_cdemPair005 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 81920 (.branch mobiusTableBlock010 mobiusTableBlock011) = true := mobiusValuePair005_checked

lemma cdem_prefix_assembled_cdemPair006 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 98304 (.branch mobiusTableBlock012 mobiusTableBlock013) = true := mobiusValuePair006_checked

lemma cdem_prefix_assembled_cdemPair007 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 114688 (.branch mobiusTableBlock014 mobiusTableBlock015) = true := mobiusValuePair007_checked

lemma cdem_prefix_assembled_cdemPair008 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 131072 (.branch mobiusTableBlock016 mobiusTableBlock017) = true := mobiusValuePair008_checked

lemma cdem_prefix_assembled_cdemPair009 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 147456 (.branch mobiusTableBlock018 mobiusTableBlock019) = true := mobiusValuePair009_checked

lemma cdem_prefix_assembled_cdemPair010 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 163840 (.branch mobiusTableBlock020 mobiusTableBlock021) = true := mobiusValuePair010_checked

lemma cdem_prefix_assembled_cdemPair011 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 180224 (.branch mobiusTableBlock022 mobiusTableBlock023) = true := mobiusValuePair011_checked

lemma cdem_prefix_assembled_cdemPair012 : mobiusTreeCheck cdem_prefix_assembled_cdemCandidateMu 1200001 9 196608 (.branch mobiusTableBlock024 mobiusTableBlock025) = true := mobiusValuePair012_checked

theorem cdem_prefix_assembled_cdem_candidate_mu_eq (n : ℕ) (hn : n ≤ 199330) : cdem_prefix_assembled_cdemCandidateMu n = moebius n := by
  have hall : ∀ k < 199331, cdem_prefix_assembled_cdemCandidateMu k = moebius k := by
    apply cdem_prefix_assembled_moebius_of_local_checks cdem_prefix_assembled_cdemCandidateMu 199331 (by norm_num)
    intro k hk
    by_cases h0 : k < 16384
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 0
        (.branch mobiusTableBlock000 mobiusTableBlock001) cdem_prefix_assembled_cdemPair000
        k (by omega) (by omega) (by omega)
    by_cases h1 : k < 32768
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 16384
        (.branch mobiusTableBlock002 mobiusTableBlock003) cdem_prefix_assembled_cdemPair001
        k (by omega) (by omega) (by omega)
    by_cases h2 : k < 49152
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 32768
        (.branch mobiusTableBlock004 mobiusTableBlock005) cdem_prefix_assembled_cdemPair002
        k (by omega) (by omega) (by omega)
    by_cases h3 : k < 65536
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 49152
        (.branch mobiusTableBlock006 mobiusTableBlock007) cdem_prefix_assembled_cdemPair003
        k (by omega) (by omega) (by omega)
    by_cases h4 : k < 81920
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 65536
        (.branch mobiusTableBlock008 mobiusTableBlock009) cdem_prefix_assembled_cdemPair004
        k (by omega) (by omega) (by omega)
    by_cases h5 : k < 98304
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 81920
        (.branch mobiusTableBlock010 mobiusTableBlock011) cdem_prefix_assembled_cdemPair005
        k (by omega) (by omega) (by omega)
    by_cases h6 : k < 114688
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 98304
        (.branch mobiusTableBlock012 mobiusTableBlock013) cdem_prefix_assembled_cdemPair006
        k (by omega) (by omega) (by omega)
    by_cases h7 : k < 131072
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 114688
        (.branch mobiusTableBlock014 mobiusTableBlock015) cdem_prefix_assembled_cdemPair007
        k (by omega) (by omega) (by omega)
    by_cases h8 : k < 147456
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 131072
        (.branch mobiusTableBlock016 mobiusTableBlock017) cdem_prefix_assembled_cdemPair008
        k (by omega) (by omega) (by omega)
    by_cases h9 : k < 163840
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 147456
        (.branch mobiusTableBlock018 mobiusTableBlock019) cdem_prefix_assembled_cdemPair009
        k (by omega) (by omega) (by omega)
    by_cases h10 : k < 180224
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 163840
        (.branch mobiusTableBlock020 mobiusTableBlock021) cdem_prefix_assembled_cdemPair010
        k (by omega) (by omega) (by omega)
    by_cases h11 : k < 196608
    · exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 180224
        (.branch mobiusTableBlock022 mobiusTableBlock023) cdem_prefix_assembled_cdemPair011
        k (by omega) (by omega) (by omega)
    exact cdem_prefix_assembled_mobiusTreeCheck_local_sound cdem_prefix_assembled_cdemCandidateMu 1200001 9 196608
      (.branch mobiusTableBlock024 mobiusTableBlock025) cdem_prefix_assembled_cdemPair012
      k (by omega) (by omega) (by omega)
  exact hall n (by omega)
end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators
namespace Helfgott

lemma cdem_prefix_assembled_reciprocal_integer_rounding_error (Q n : ℕ) (a : ℤ)
    (hQ : 0 < Q) (hn : 0 < n) (ha : |a| ≤ 1) :
    |(a : ℝ) / (n : ℝ) - (a : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)| ≤
      1 / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have har : |(a : ℝ)| ≤ 1 := by exact_mod_cast ha
  have hf : |(Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ)| ≤ 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.abs_sub_floor_le (a := (Q : ℝ) / (n : ℝ)) (by positivity))
  have he : (a : ℝ) / (n : ℝ) - (a : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ) =
      (a : ℝ) * ((Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ)) / (Q : ℝ) := by
    field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hQr]
  exact div_le_div_of_nonneg_right
    (by nlinarith [abs_nonneg (a : ℝ), abs_nonneg ((Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ))]) hQr.le

theorem cdem_prefix_assembled_moebius_reciprocal_rounded_sum_error (Q N : ℕ) (hQ : 0 < Q) :
    |(∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) -
      (((∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) : ℤ) : ℝ) / (Q : ℝ)| ≤
      (N : ℝ) / (Q : ℝ) := by
  have he : (∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) -
      (((∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) : ℤ) : ℝ) / (Q : ℝ) =
      ∑ n ∈ Finset.Icc 1 N,
        (((moebius n : ℤ) : ℝ) / (n : ℝ) -
          ((moebius n : ℤ) : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        |((moebius n : ℤ) : ℝ) / (n : ℝ) -
          ((moebius n : ℤ) : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact cdem_prefix_assembled_reciprocal_integer_rounding_error Q n (moebius n) hQ
        (by have := (Finset.mem_Icc.mp hn).1; omega) abs_moebius_le_one
    _ = (N : ℝ) / (Q : ℝ) := by simp [Nat.card_Icc, div_eq_mul_inv]

theorem cdem_prefix_assembled_moebius_reciprocal_of_rounded_sum (Q N : ℕ) (S : ℤ) (hQ : 0 < Q)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) :
    |∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      ((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have he := cdem_prefix_assembled_moebius_reciprocal_rounded_sum_error Q N hQ
  rw [← hS] at he
  have ht := abs_add_le
    ((∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) - (S : ℝ) / (Q : ℝ))
    ((S : ℝ) / (Q : ℝ))
  rw [sub_add_cancel, abs_div, abs_of_pos hQr] at ht
  have habs : |(S : ℝ)| = (S.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [habs] at ht
  exact ht.trans (by rw [add_div]; linarith [he])

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma cdem_prefix_assembled_cdem_sum_icc_eq_ico {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (hf : f 0 = 0) (K : ℕ) :
    (∑ n ∈ Icc 1 K, f n) = ∑ n ∈ Ico 0 (K+1), f n := by
  have hsplit := Finset.sum_Ico_consecutive f
    (by norm_num : 0 ≤ 1) (by omega : 1 ≤ K+1)
  have hzero : (∑ n ∈ Ico 0 1, f n) = 0 := by simp [hf]
  rw [hzero, zero_add] at hsplit
  rw [← Finset.Ico_succ_right_eq_Icc]
  exact hsplit

theorem cdem_prefix_assembled_cdem_prefix_of_integer_totals (g : ℕ → ℤ)
    (hg : ∀ n ≤ 199330, g n = moebius n)
    (hM : (∑ n ∈ Ico 0 199331, g n) = (-6 : ℤ))
    (hS : (∑ n ∈ Ico 0 199331, (g n).natAbs) = 121174)
    (hF : (∑ n ∈ Ico 0 199331, g n * (5000000000 / n : ℕ)) = (112 : ℤ))
    (hR : (∑ n ∈ Ico 0 199331, g n *
      (100000000000000000000000000000000 / n : ℕ)) =
      (2098595765597847108232803 : ℤ)) :
    (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) ∧
    (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 ∧
    (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) ∧
    (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ) := by
  have hsum {A : Type} [AddCommMonoid A] (f : ℤ → ℕ → A)
      (hf : f 0 0 = 0) :
      (∑ n ∈ Icc 1 199330, f (moebius n) n) =
        ∑ n ∈ Ico 0 199331, f (g n) n := by
    rw [cdem_prefix_assembled_cdem_sum_icc_eq_ico (fun n => f (moebius n) n) (by simpa using hf)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hg n (by have := Finset.mem_Ico.mp hn; omega)]
  have hMa : (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) := by
    rw [hsum (A := ℤ) (fun a _ => a) rfl]
    exact hM
  have hSa : (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 := by
    rw [hsum (A := ℕ) (fun a _ => a.natAbs) rfl]
    exact hS
  have hFa : (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) := by
    rw [hsum (A := ℤ) (fun a n => a * (5000000000 / n : ℕ)) (by simp)]
    exact hF
  have hRa : (∑ n ∈ Icc 1 199330, moebius n *
      (100000000000000000000000000000000 / n : ℕ)) =
      (2098595765597847108232803 : ℤ) := by
    rw [hsum (A := ℤ) (fun a n => a * (100000000000000000000000000000000 / n : ℕ)) (by simp)]
    exact hR
  have herr := cdem_prefix_assembled_moebius_reciprocal_rounded_sum_error
    100000000000000000000000000000000 199330 (by norm_num)
  rw [hRa] at herr
  have htwo := abs_le.mp herr
  refine ⟨hMa, hSa, hFa, ?_, ?_⟩ <;>
    norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at htwo <;>
    linarith [htwo.1, htwo.2]

lemma cdem_prefix_assembled_cdem_endpoint_reciprocal_sqrt :
    1 / Real.sqrt (5000000001 : ℝ) ≤
      (14142135622317 / 1000000000000000000 : ℝ) := by
  have hs0 : (0 : ℝ) < Real.sqrt 5000000001 := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5000000001)
  have hbound : (1000000000000000000 / 14142135622317 : ℝ) ≤
      Real.sqrt 5000000001 := by
    nlinarith [Real.sqrt_nonneg (5000000001 : ℝ)]
  apply (div_le_iff₀ hs0).2
  nlinarith [hbound]

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
open Finset
open scoped BigOperators
namespace Helfgott

lemma cdem_prefix_assembled_cdem_integer_totals_join (g : ℕ → ℤ) (a c b : ℕ)
    (ha : a ≤ c) (hb : c ≤ b)
    (N Q : ℕ) (m1 m2 f1 f2 r1 r2 : ℤ) (s1 s2 : ℕ)
    (h1 : (∑ n ∈ Ico a c, g n) = m1 ∧
      (∑ n ∈ Ico a c, (g n).natAbs) = s1 ∧
      (∑ n ∈ Ico a c, g n*(N/n : ℕ)) = f1 ∧
      (∑ n ∈ Ico a c, g n*(Q/n : ℕ)) = r1)
    (h2 : (∑ n ∈ Ico c b, g n) = m2 ∧
      (∑ n ∈ Ico c b, (g n).natAbs) = s2 ∧
      (∑ n ∈ Ico c b, g n*(N/n : ℕ)) = f2 ∧
      (∑ n ∈ Ico c b, g n*(Q/n : ℕ)) = r2) :
    (∑ n ∈ Ico a b, g n) = m1+m2 ∧
    (∑ n ∈ Ico a b, (g n).natAbs) = s1+s2 ∧
    (∑ n ∈ Ico a b, g n*(N/n : ℕ)) = f1+f2 ∧
    (∑ n ∈ Ico a b, g n*(Q/n : ℕ)) = r1+r2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Finset.sum_Ico_consecutive g ha hb).symm.trans
      (congrArg₂ (fun u v : ℤ => u+v) h1.1 h2.1)
  · exact (Finset.sum_Ico_consecutive (fun n => (g n).natAbs) ha hb).symm.trans
      (congrArg₂ (fun u v : ℕ => u+v) h1.2.1 h2.2.1)
  · exact (Finset.sum_Ico_consecutive (fun n => g n*(N/n : ℕ)) ha hb).symm.trans
      (congrArg₂ (fun u v : ℤ => u+v) h1.2.2.1 h2.2.2.1)
  · exact (Finset.sum_Ico_consecutive (fun n => g n*(Q/n : ℕ)) ha hb).symm.trans
      (congrArg₂ (fun u v : ℤ => u+v) h1.2.2.2 h2.2.2.2)

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott
lemma cdem_prefix_assembled_cdemPrefixFastStats_4096_12288 :
    (∑ n ∈ Ico 4096 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (40 : ℤ) ∧
    (∑ n ∈ Ico 4096 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4978 : ℕ) ∧
    (∑ n ∈ Ico 4096 12288, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (29960262 : ℤ) ∧
    (∑ n ∈ Ico 4096 12288, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (599205325600187899165154739906 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    4096 8192 12288 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (41 : ℤ) (-1 : ℤ) (34957511 : ℤ) (-4997249 : ℤ) (699150512321253056761886786107 : ℤ) (-99945186721065157596732046201 : ℤ) 2491 2487
    cdemPrefixGroup001_checked cdemPrefixGroup002_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_0_12288 :
    (∑ n ∈ Ico 0 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 0 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7469 : ℕ) ∧
    (∑ n ∈ Ico 0 12288, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (9375231 : ℤ) ∧
    (∑ n ∈ Ico 0 12288, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (187504656391998837042310053501 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    0 4096 12288 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-19 : ℤ) (40 : ℤ) (-20585031 : ℤ) (29960262 : ℤ) (-411700669208189062122844686405 : ℤ) (599205325600187899165154739906 : ℤ) 2491 4978
    cdemPrefixGroup000_checked cdem_prefix_assembled_cdemPrefixFastStats_4096_12288
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_16384_24576 :
    (∑ n ∈ Ico 16384 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 16384 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4977 : ℕ) ∧
    (∑ n ∈ Ico 16384 24576, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-1302727 : ℤ) ∧
    (∑ n ∈ Ico 16384 24576, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-26054426213487825512763849293 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    16384 20480 24576 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (55 : ℤ) (-76 : ℤ) (15458647 : ℤ) (-16761374 : ℤ) (309173526311773485610560359558 : ℤ) (-335227952525261311123324208851 : ℤ) 2491 2486
    cdemPrefixGroup004_checked cdemPrefixGroup005_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_12288_24576 :
    (∑ n ∈ Ico 12288 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-74 : ℤ) ∧
    (∑ n ∈ Ico 12288 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7470 : ℕ) ∧
    (∑ n ∈ Ico 12288 24576, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-19880856 : ℤ) ∧
    (∑ n ∈ Ico 12288 24576, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-397617036647351254858530785197 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    12288 16384 24576 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-53 : ℤ) (-21 : ℤ) (-18578129 : ℤ) (-1302727 : ℤ) (-371562610433863429345766935904 : ℤ) (-26054426213487825512763849293 : ℤ) 2493 4977
    cdemPrefixGroup003_checked cdem_prefix_assembled_cdemPrefixFastStats_16384_24576
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_0_24576 :
    (∑ n ∈ Ico 0 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-53 : ℤ) ∧
    (∑ n ∈ Ico 0 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14939 : ℕ) ∧
    (∑ n ∈ Ico 0 24576, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-10505625 : ℤ) ∧
    (∑ n ∈ Ico 0 24576, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-210112380255352417816220731696 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    0 12288 24576 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (21 : ℤ) (-74 : ℤ) (9375231 : ℤ) (-19880856 : ℤ) (187504656391998837042310053501 : ℤ) (-397617036647351254858530785197 : ℤ) 7469 7470
    cdem_prefix_assembled_cdemPrefixFastStats_0_12288 cdem_prefix_assembled_cdemPrefixFastStats_12288_24576
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_28672_36864 :
    (∑ n ∈ Ico 28672 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 28672 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4977 : ℕ) ∧
    (∑ n ∈ Ico 28672 36864, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1108745 : ℤ) ∧
    (∑ n ∈ Ico 28672 36864, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (22175158061270184463318839746 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    28672 32768 36864 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (36 : ℤ) (-33 : ℤ) (6229467 : ℤ) (-5120722 : ℤ) (124590055446270867968603592582 : ℤ) (-102414897385000683505284752836 : ℤ) 2486 2491
    cdemPrefixGroup007_checked cdemPrefixGroup008_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_24576_36864 :
    (∑ n ∈ Ico 24576 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (46 : ℤ) ∧
    (∑ n ∈ Ico 24576 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7472 : ℕ) ∧
    (∑ n ∈ Ico 24576 36864, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (9990992 : ℤ) ∧
    (∑ n ∈ Ico 24576 36864, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (199820364636187846502111361477 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    24576 28672 36864 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (43 : ℤ) (3 : ℤ) (8882247 : ℤ) (1108745 : ℤ) (177645206574917662038792521731 : ℤ) (22175158061270184463318839746 : ℤ) 2495 4977
    cdemPrefixGroup006_checked cdem_prefix_assembled_cdemPrefixFastStats_28672_36864
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_40960_49152 :
    (∑ n ∈ Ico 40960 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (84 : ℤ) ∧
    (∑ n ∈ Ico 40960 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4992 : ℕ) ∧
    (∑ n ∈ Ico 40960 49152, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (8752716 : ℤ) ∧
    (∑ n ∈ Ico 40960 49152, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (175055122145686399670983745912 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    40960 45056 49152 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (8 : ℤ) (76 : ℤ) (630528 : ℤ) (8122188 : ℤ) (12610742463242094854335621693 : ℤ) (162444379682444304816648124219 : ℤ) 2500 2492
    cdemPrefixGroup010_checked cdemPrefixGroup011_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_36864_49152 :
    (∑ n ∈ Ico 36864 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (85 : ℤ) ∧
    (∑ n ∈ Ico 36864 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7475 : ℕ) ∧
    (∑ n ∈ Ico 36864 49152, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (8724704 : ℤ) ∧
    (∑ n ∈ Ico 36864 49152, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (174494616312704771787820661630 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    36864 40960 49152 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (1 : ℤ) (84 : ℤ) (-28012 : ℤ) (8752716 : ℤ) (-560505832981627883163084282 : ℤ) (175055122145686399670983745912 : ℤ) 2483 4992
    cdemPrefixGroup009_checked cdem_prefix_assembled_cdemPrefixFastStats_40960_49152
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_24576_49152 :
    (∑ n ∈ Ico 24576 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (131 : ℤ) ∧
    (∑ n ∈ Ico 24576 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14947 : ℕ) ∧
    (∑ n ∈ Ico 24576 49152, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (18715696 : ℤ) ∧
    (∑ n ∈ Ico 24576 49152, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (374314980948892618289932023107 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    24576 36864 49152 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (46 : ℤ) (85 : ℤ) (9990992 : ℤ) (8724704 : ℤ) (199820364636187846502111361477 : ℤ) (174494616312704771787820661630 : ℤ) 7472 7475
    cdem_prefix_assembled_cdemPrefixFastStats_24576_36864 cdem_prefix_assembled_cdemPrefixFastStats_36864_49152
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_0_49152 :
    (∑ n ∈ Ico 0 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (78 : ℤ) ∧
    (∑ n ∈ Ico 0 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (29886 : ℕ) ∧
    (∑ n ∈ Ico 0 49152, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (8210071 : ℤ) ∧
    (∑ n ∈ Ico 0 49152, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (164202600693540200473711291411 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    0 24576 49152 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-53 : ℤ) (131 : ℤ) (-10505625 : ℤ) (18715696 : ℤ) (-210112380255352417816220731696 : ℤ) (374314980948892618289932023107 : ℤ) 14939 14947
    cdem_prefix_assembled_cdemPrefixFastStats_0_24576 cdem_prefix_assembled_cdemPrefixFastStats_24576_49152
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_53248_61440 :
    (∑ n ∈ Ico 53248 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (-66 : ℤ) ∧
    (∑ n ∈ Ico 53248 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4978 : ℕ) ∧
    (∑ n ∈ Ico 53248 61440, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-5944112 : ℤ) ∧
    (∑ n ∈ Ico 53248 61440, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-118882919134244077913940683704 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    53248 57344 61440 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-74 : ℤ) (8 : ℤ) (-6526262 : ℤ) (582150 : ℤ) (-130525671446891319381165871871 : ℤ) (11642752312647241467225188167 : ℤ) 2484 2494
    cdemPrefixGroup013_checked cdemPrefixGroup014_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_49152_61440 :
    (∑ n ∈ Ico 49152 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (-132 : ℤ) ∧
    (∑ n ∈ Ico 49152 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7468 : ℕ) ∧
    (∑ n ∈ Ico 49152 61440, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-12568472 : ℤ) ∧
    (∑ n ∈ Ico 49152 61440, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-251370937060745991275655581448 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    49152 53248 61440 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-66 : ℤ) (-66 : ℤ) (-6624360 : ℤ) (-5944112 : ℤ) (-132488017926501913361714897744 : ℤ) (-118882919134244077913940683704 : ℤ) 2490 4978
    cdemPrefixGroup012_checked cdem_prefix_assembled_cdemPrefixFastStats_53248_61440
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_65536_73728 :
    (∑ n ∈ Ico 65536 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 65536 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4976 : ℕ) ∧
    (∑ n ∈ Ico 65536 73728, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1704970 : ℤ) ∧
    (∑ n ∈ Ico 65536 73728, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (34099613637593057134359592448 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    65536 69632 73728 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (78 : ℤ) (-56 : ℤ) (5693314 : ℤ) (-3988344 : ℤ) (113867298783621895407740232468 : ℤ) (-79767685146028838273380640020 : ℤ) 2486 2490
    cdemPrefixGroup016_checked cdemPrefixGroup017_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_61440_73728 :
    (∑ n ∈ Ico 61440 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (90 : ℤ) ∧
    (∑ n ∈ Ico 61440 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7466 : ℕ) ∧
    (∑ n ∈ Ico 61440 73728, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (6957737 : ℤ) ∧
    (∑ n ∈ Ico 61440 73728, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (139155724402898259924377966460 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    61440 65536 73728 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (68 : ℤ) (22 : ℤ) (5252767 : ℤ) (1704970 : ℤ) (105056110765305202790018374012 : ℤ) (34099613637593057134359592448 : ℤ) 2490 4976
    cdemPrefixGroup015_checked cdem_prefix_assembled_cdemPrefixFastStats_65536_73728
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_49152_73728 :
    (∑ n ∈ Ico 49152 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 49152 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14934 : ℕ) ∧
    (∑ n ∈ Ico 49152 73728, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-5610735 : ℤ) ∧
    (∑ n ∈ Ico 49152 73728, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-112215212657847731351277614988 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    49152 61440 73728 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-132 : ℤ) (90 : ℤ) (-12568472 : ℤ) (6957737 : ℤ) (-251370937060745991275655581448 : ℤ) (139155724402898259924377966460 : ℤ) 7468 7466
    cdem_prefix_assembled_cdemPrefixFastStats_49152_61440 cdem_prefix_assembled_cdemPrefixFastStats_61440_73728
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_77824_86016 :
    (∑ n ∈ Ico 77824 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (71 : ℤ) ∧
    (∑ n ∈ Ico 77824 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4981 : ℕ) ∧
    (∑ n ∈ Ico 77824 86016, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (4160598 : ℤ) ∧
    (∑ n ∈ Ico 77824 86016, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (83212440304508450439809416561 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    77824 81920 86016 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-11 : ℤ) (82 : ℤ) (-636009 : ℤ) (4796607 : ℤ) (-12720418578954713761090633101 : ℤ) (95932858883463164200900049662 : ℤ) 2487 2494
    cdemPrefixGroup019_checked cdemPrefixGroup020_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_73728_86016 :
    (∑ n ∈ Ico 73728 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 73728 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7467 : ℕ) ∧
    (∑ n ∈ Ico 73728 86016, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1148934 : ℤ) ∧
    (∑ n ∈ Ico 73728 86016, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (22978618752279394200554303360 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    73728 77824 86016 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-46 : ℤ) (71 : ℤ) (-3011664 : ℤ) (4160598 : ℤ) (-60233821552229056239255113201 : ℤ) (83212440304508450439809416561 : ℤ) 2486 4981
    cdemPrefixGroup018_checked cdem_prefix_assembled_cdemPrefixFastStats_77824_86016
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_90112_98304 :
    (∑ n ∈ Ico 90112 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-67 : ℤ) ∧
    (∑ n ∈ Ico 90112 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4981 : ℕ) ∧
    (∑ n ∈ Ico 90112 98304, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-3635543 : ℤ) ∧
    (∑ n ∈ Ico 90112 98304, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-72711711996932858399057909865 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    90112 94208 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-62 : ℤ) (-5 : ℤ) (-3317294 : ℤ) (-318249 : ℤ) (-66346628080622312589865919477 : ℤ) (-6365083916310545809191990388 : ℤ) 2496 2485
    cdemPrefixGroup022_checked cdemPrefixGroup023_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_86016_98304 :
    (∑ n ∈ Ico 86016 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-137 : ℤ) ∧
    (∑ n ∈ Ico 86016 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7475 : ℕ) ∧
    (∑ n ∈ Ico 86016 98304, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-7596879 : ℤ) ∧
    (∑ n ∈ Ico 86016 98304, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-151939040957450744289205935106 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    86016 90112 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-70 : ℤ) (-67 : ℤ) (-3961336 : ℤ) (-3635543 : ℤ) (-79227328960517885890148025241 : ℤ) (-72711711996932858399057909865 : ℤ) 2494 4981
    cdemPrefixGroup021_checked cdem_prefix_assembled_cdemPrefixFastStats_90112_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_73728_98304 :
    (∑ n ∈ Ico 73728 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-112 : ℤ) ∧
    (∑ n ∈ Ico 73728 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14942 : ℕ) ∧
    (∑ n ∈ Ico 73728 98304, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-6447945 : ℤ) ∧
    (∑ n ∈ Ico 73728 98304, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-128960422205171350088651631746 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    73728 86016 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (25 : ℤ) (-137 : ℤ) (1148934 : ℤ) (-7596879 : ℤ) (22978618752279394200554303360 : ℤ) (-151939040957450744289205935106 : ℤ) 7467 7475
    cdem_prefix_assembled_cdemPrefixFastStats_73728_86016 cdem_prefix_assembled_cdemPrefixFastStats_86016_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_49152_98304 :
    (∑ n ∈ Ico 49152 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-154 : ℤ) ∧
    (∑ n ∈ Ico 49152 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (29876 : ℕ) ∧
    (∑ n ∈ Ico 49152 98304, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-12058680 : ℤ) ∧
    (∑ n ∈ Ico 49152 98304, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-241175634863019081439929246734 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    49152 73728 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-42 : ℤ) (-112 : ℤ) (-5610735 : ℤ) (-6447945 : ℤ) (-112215212657847731351277614988 : ℤ) (-128960422205171350088651631746 : ℤ) 14934 14942
    cdem_prefix_assembled_cdemPrefixFastStats_49152_73728 cdem_prefix_assembled_cdemPrefixFastStats_73728_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_0_98304 :
    (∑ n ∈ Ico 0 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-76 : ℤ) ∧
    (∑ n ∈ Ico 0 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (59762 : ℕ) ∧
    (∑ n ∈ Ico 0 98304, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-3848609 : ℤ) ∧
    (∑ n ∈ Ico 0 98304, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-76973034169478880966217955323 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    0 49152 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (78 : ℤ) (-154 : ℤ) (8210071 : ℤ) (-12058680 : ℤ) (164202600693540200473711291411 : ℤ) (-241175634863019081439929246734 : ℤ) 29886 29876
    cdem_prefix_assembled_cdemPrefixFastStats_0_49152 cdem_prefix_assembled_cdemPrefixFastStats_49152_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_102400_110592 :
    (∑ n ∈ Ico 102400 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (63 : ℤ) ∧
    (∑ n ∈ Ico 102400 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4979 : ℕ) ∧
    (∑ n ∈ Ico 102400 110592, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (3015184 : ℤ) ∧
    (∑ n ∈ Ico 102400 110592, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (60304387908863887576143585496 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    102400 106496 110592 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (29 : ℤ) (34 : ℤ) (1431362 : ℤ) (1583822 : ℤ) (28627378348167438853142479503 : ℤ) (31677009560696448723001105993 : ℤ) 2487 2492
    cdemPrefixGroup025_checked cdemPrefixGroup026_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_98304_110592 :
    (∑ n ∈ Ico 98304 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (80 : ℤ) ∧
    (∑ n ∈ Ico 98304 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7478 : ℕ) ∧
    (∑ n ∈ Ico 98304 110592, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (3911688 : ℤ) ∧
    (∑ n ∈ Ico 98304 110592, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (78234295464644624489442389926 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98304 102400 110592 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (17 : ℤ) (63 : ℤ) (896504 : ℤ) (3015184 : ℤ) (17929907555780736913298804430 : ℤ) (60304387908863887576143585496 : ℤ) 2499 4979
    cdemPrefixGroup024_checked cdem_prefix_assembled_cdemPrefixFastStats_102400_110592
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_114688_122880 :
    (∑ n ∈ Ico 114688 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-52 : ℤ) ∧
    (∑ n ∈ Ico 114688 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4970 : ℕ) ∧
    (∑ n ∈ Ico 114688 122880, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-2122009 : ℤ) ∧
    (∑ n ∈ Ico 114688 122880, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-42439885221025906006988398477 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    114688 118784 122880 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (15 : ℤ) (-67 : ℤ) (631054 : ℤ) (-2753063 : ℤ) (12621962507031227870189260397 : ℤ) (-55061847728057133877177658874 : ℤ) 2483 2487
    cdemPrefixGroup028_checked cdemPrefixGroup029_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_110592_122880 :
    (∑ n ∈ Ico 110592 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 110592 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7455 : ℕ) ∧
    (∑ n ∈ Ico 110592 122880, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1736368 : ℤ) ∧
    (∑ n ∈ Ico 110592 122880, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (34728685588449805073125124404 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    110592 114688 122880 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (87 : ℤ) (-52 : ℤ) (3858377 : ℤ) (-2122009 : ℤ) (77168570809475711080113522881 : ℤ) (-42439885221025906006988398477 : ℤ) 2485 4970
    cdemPrefixGroup027_checked cdem_prefix_assembled_cdemPrefixFastStats_114688_122880
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_98304_122880 :
    (∑ n ∈ Ico 98304 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (115 : ℤ) ∧
    (∑ n ∈ Ico 98304 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14933 : ℕ) ∧
    (∑ n ∈ Ico 98304 122880, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (5648056 : ℤ) ∧
    (∑ n ∈ Ico 98304 122880, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (112962981053094429562567514330 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98304 110592 122880 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (80 : ℤ) (35 : ℤ) (3911688 : ℤ) (1736368 : ℤ) (78234295464644624489442389926 : ℤ) (34728685588449805073125124404 : ℤ) 7478 7455
    cdem_prefix_assembled_cdemPrefixFastStats_98304_110592 cdem_prefix_assembled_cdemPrefixFastStats_110592_122880
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_126976_135168 :
    (∑ n ∈ Ico 126976 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 126976 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4975 : ℕ) ∧
    (∑ n ∈ Ico 126976 135168, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-898700 : ℤ) ∧
    (∑ n ∈ Ico 126976 135168, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-17974422196153918264552081308 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    126976 131072 135168 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-48 : ℤ) (25 : ℤ) (-1828624 : ℤ) (929924 : ℤ) (-36572934278886159193432981618 : ℤ) (18598512082732240928880900310 : ℤ) 2492 2483
    cdemPrefixGroup031_checked cdemPrefixGroup032_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_122880_135168 :
    (∑ n ∈ Ico 122880 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (-34 : ℤ) ∧
    (∑ n ∈ Ico 122880 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7476 : ℕ) ∧
    (∑ n ∈ Ico 122880 135168, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-1354145 : ℤ) ∧
    (∑ n ∈ Ico 122880 135168, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-27083619572174835104317785146 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    122880 126976 135168 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-11 : ℤ) (-23 : ℤ) (-455445 : ℤ) (-898700 : ℤ) (-9109197376020916839765703838 : ℤ) (-17974422196153918264552081308 : ℤ) 2501 4975
    cdemPrefixGroup030_checked cdem_prefix_assembled_cdemPrefixFastStats_126976_135168
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_139264_147456 :
    (∑ n ∈ Ico 139264 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (38 : ℤ) ∧
    (∑ n ∈ Ico 139264 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4982 : ℕ) ∧
    (∑ n ∈ Ico 139264 147456, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1333971 : ℤ) ∧
    (∑ n ∈ Ico 139264 147456, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (26679866091566454340359692932 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    139264 143360 147456 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (36 : ℤ) (2 : ℤ) (1256218 : ℤ) (77753 : ℤ) (25125034322283821108684733129 : ℤ) (1554831769282633231674959803 : ℤ) 2496 2486
    cdemPrefixGroup034_checked cdemPrefixGroup035_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_135168_147456 :
    (∑ n ∈ Ico 135168 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 135168 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7476 : ℕ) ∧
    (∑ n ∈ Ico 135168 147456, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-2320097 : ℤ) ∧
    (∑ n ∈ Ico 135168 147456, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-46402584856435134976936054112 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    135168 139264 147456 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-100 : ℤ) (38 : ℤ) (-3654068 : ℤ) (1333971 : ℤ) (-73082450948001589317295747044 : ℤ) (26679866091566454340359692932 : ℤ) 2494 4982
    cdemPrefixGroup033_checked cdem_prefix_assembled_cdemPrefixFastStats_139264_147456
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_122880_147456 :
    (∑ n ∈ Ico 122880 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (-96 : ℤ) ∧
    (∑ n ∈ Ico 122880 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14952 : ℕ) ∧
    (∑ n ∈ Ico 122880 147456, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-3674242 : ℤ) ∧
    (∑ n ∈ Ico 122880 147456, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-73486204428609970081253839258 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    122880 135168 147456 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-34 : ℤ) (-62 : ℤ) (-1354145 : ℤ) (-2320097 : ℤ) (-27083619572174835104317785146 : ℤ) (-46402584856435134976936054112 : ℤ) 7476 7476
    cdem_prefix_assembled_cdemPrefixFastStats_122880_135168 cdem_prefix_assembled_cdemPrefixFastStats_135168_147456
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_98304_147456 :
    (∑ n ∈ Ico 98304 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 98304 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (29885 : ℕ) ∧
    (∑ n ∈ Ico 98304 147456, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1973814 : ℤ) ∧
    (∑ n ∈ Ico 98304 147456, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (39476776624484459481313675072 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98304 122880 147456 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (115 : ℤ) (-96 : ℤ) (5648056 : ℤ) (-3674242 : ℤ) (112962981053094429562567514330 : ℤ) (-73486204428609970081253839258 : ℤ) 14933 14952
    cdem_prefix_assembled_cdemPrefixFastStats_98304_122880 cdem_prefix_assembled_cdemPrefixFastStats_122880_147456
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_151552_159744 :
    (∑ n ∈ Ico 151552 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-30 : ℤ) ∧
    (∑ n ∈ Ico 151552 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4976 : ℕ) ∧
    (∑ n ∈ Ico 151552 159744, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-998870 : ℤ) ∧
    (∑ n ∈ Ico 151552 159744, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-19977688336240796180907427750 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    151552 155648 159744 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-26 : ℤ) (-4 : ℤ) (-874471 : ℤ) (-124399 : ℤ) (-17489729376966159644790271834 : ℤ) (-2487958959274636536117155916 : ℤ) 2486 2490
    cdemPrefixGroup037_checked cdemPrefixGroup038_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_147456_159744 :
    (∑ n ∈ Ico 147456 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 147456 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7468 : ℕ) ∧
    (∑ n ∈ Ico 147456 159744, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-333492 : ℤ) ∧
    (∑ n ∈ Ico 147456 159744, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-6670399725302507164916961168 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    147456 151552 159744 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (20 : ℤ) (-30 : ℤ) (665378 : ℤ) (-998870 : ℤ) (13307288610938289015990466582 : ℤ) (-19977688336240796180907427750 : ℤ) 2492 4976
    cdemPrefixGroup036_checked cdem_prefix_assembled_cdemPrefixFastStats_151552_159744
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_163840_172032 :
    (∑ n ∈ Ico 163840 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (76 : ℤ) ∧
    (∑ n ∈ Ico 163840 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4982 : ℕ) ∧
    (∑ n ∈ Ico 163840 172032, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (2294979 : ℤ) ∧
    (∑ n ∈ Ico 163840 172032, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (45899753403924151115688141505 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    163840 167936 172032 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (46 : ℤ) (30 : ℤ) (1390733 : ℤ) (904246 : ℤ) (27814957145438392547713550359 : ℤ) (18084796258485758567974591146 : ℤ) 2492 2490
    cdemPrefixGroup040_checked cdemPrefixGroup041_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_159744_172032 :
    (∑ n ∈ Ico 159744 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (148 : ℤ) ∧
    (∑ n ∈ Ico 159744 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7464 : ℕ) ∧
    (∑ n ∈ Ico 159744 172032, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (4518527 : ℤ) ∧
    (∑ n ∈ Ico 159744 172032, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (90371481886900895692925872662 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    159744 163840 172032 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (72 : ℤ) (76 : ℤ) (2223548 : ℤ) (2294979 : ℤ) (44471728482976744577237731157 : ℤ) (45899753403924151115688141505 : ℤ) 2482 4982
    cdemPrefixGroup039_checked cdem_prefix_assembled_cdemPrefixFastStats_163840_172032
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_147456_172032 :
    (∑ n ∈ Ico 147456 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (138 : ℤ) ∧
    (∑ n ∈ Ico 147456 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (14932 : ℕ) ∧
    (∑ n ∈ Ico 147456 172032, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (4185035 : ℤ) ∧
    (∑ n ∈ Ico 147456 172032, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (83701082161598388528008911494 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    147456 159744 172032 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-10 : ℤ) (148 : ℤ) (-333492 : ℤ) (4518527 : ℤ) (-6670399725302507164916961168 : ℤ) (90371481886900895692925872662 : ℤ) 7468 7464
    cdem_prefix_assembled_cdemPrefixFastStats_147456_159744 cdem_prefix_assembled_cdemPrefixFastStats_159744_172032
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_176128_184320 :
    (∑ n ∈ Ico 176128 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-76 : ℤ) ∧
    (∑ n ∈ Ico 176128 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4986 : ℕ) ∧
    (∑ n ∈ Ico 176128 184320, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-2108410 : ℤ) ∧
    (∑ n ∈ Ico 176128 184320, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-42168815107741550398274641442 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    176128 180224 184320 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-33 : ℤ) (-43 : ℤ) (-935760 : ℤ) (-1172650 : ℤ) (-18715745290123822870982040564 : ℤ) (-23453069817617727527292600878 : ℤ) 2489 2497
    cdemPrefixGroup043_checked cdemPrefixGroup044_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_172032_184320 :
    (∑ n ∈ Ico 172032 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-60 : ℤ) ∧
    (∑ n ∈ Ico 172032 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (7478 : ℕ) ∧
    (∑ n ∈ Ico 172032 184320, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-1649938 : ℤ) ∧
    (∑ n ∈ Ico 172032 184320, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-32999059220857661432554619012 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    172032 176128 184320 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (16 : ℤ) (-76 : ℤ) (458472 : ℤ) (-2108410 : ℤ) (9169755886883888965720022430 : ℤ) (-42168815107741550398274641442 : ℤ) 2492 4986
    cdemPrefixGroup042_checked cdem_prefix_assembled_cdemPrefixFastStats_176128_184320
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_184320_192512 :
    (∑ n ∈ Ico 184320 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 184320 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4977 : ℕ) ∧
    (∑ n ∈ Ico 184320 192512, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (938900 : ℤ) ∧
    (∑ n ∈ Ico 184320 192512, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (18778743509968765357459562308 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    184320 188416 192512 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (14 : ℤ) (21 : ℤ) (381835 : ℤ) (557065 : ℤ) (7636878746389338738820734466 : ℤ) (11141864763579426618638827842 : ℤ) 2488 2489
    cdemPrefixGroup045_checked cdemPrefixGroup046_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_192512_199331 :
    (∑ n ∈ Ico 192512 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 192512 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (4140 : ℕ) ∧
    (∑ n ∈ Ico 192512 199331, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-1599090 : ℤ) ∧
    (∑ n ∈ Ico 192512 199331, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-31982410309949473120901341736 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    192512 196608 199331 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-55 : ℤ) (-7 : ℤ) (-1421942 : ℤ) (-177148 : ℤ) (-28439348127680355413352485456 : ℤ) (-3543062182269117707548856280 : ℤ) 2483 1657
    cdemPrefixGroup047_checked cdemPrefixGroup048_checked
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_184320_199331 :
    (∑ n ∈ Ico 184320 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 184320 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (9117 : ℕ) ∧
    (∑ n ∈ Ico 184320 199331, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-660190 : ℤ) ∧
    (∑ n ∈ Ico 184320 199331, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-13203666799980707763441779428 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    184320 192512 199331 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (35 : ℤ) (-62 : ℤ) (938900 : ℤ) (-1599090 : ℤ) (18778743509968765357459562308 : ℤ) (-31982410309949473120901341736 : ℤ) 4977 4140
    cdem_prefix_assembled_cdemPrefixFastStats_184320_192512 cdem_prefix_assembled_cdemPrefixFastStats_192512_199331
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_172032_199331 :
    (∑ n ∈ Ico 172032 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-87 : ℤ) ∧
    (∑ n ∈ Ico 172032 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (16595 : ℕ) ∧
    (∑ n ∈ Ico 172032 199331, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (-2310128 : ℤ) ∧
    (∑ n ∈ Ico 172032 199331, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (-46202726020838369195996398440 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    172032 184320 199331 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-60 : ℤ) (-27 : ℤ) (-1649938 : ℤ) (-660190 : ℤ) (-32999059220857661432554619012 : ℤ) (-13203666799980707763441779428 : ℤ) 7478 9117
    cdem_prefix_assembled_cdemPrefixFastStats_172032_184320 cdem_prefix_assembled_cdemPrefixFastStats_184320_199331
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_147456_199331 :
    (∑ n ∈ Ico 147456 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (51 : ℤ) ∧
    (∑ n ∈ Ico 147456 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (31527 : ℕ) ∧
    (∑ n ∈ Ico 147456 199331, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (1874907 : ℤ) ∧
    (∑ n ∈ Ico 147456 199331, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (37498356140760019332012513054 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    147456 172032 199331 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (138 : ℤ) (-87 : ℤ) (4185035 : ℤ) (-2310128 : ℤ) (83701082161598388528008911494 : ℤ) (-46202726020838369195996398440 : ℤ) 14932 16595
    cdem_prefix_assembled_cdemPrefixFastStats_147456_172032 cdem_prefix_assembled_cdemPrefixFastStats_172032_199331
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_98304_199331 :
    (∑ n ∈ Ico 98304 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (70 : ℤ) ∧
    (∑ n ∈ Ico 98304 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (61412 : ℕ) ∧
    (∑ n ∈ Ico 98304 199331, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (3848721 : ℤ) ∧
    (∑ n ∈ Ico 98304 199331, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (76975132765244478813326188126 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98304 147456 199331 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (19 : ℤ) (51 : ℤ) (1973814 : ℤ) (1874907 : ℤ) (39476776624484459481313675072 : ℤ) (37498356140760019332012513054 : ℤ) 29885 31527
    cdem_prefix_assembled_cdemPrefixFastStats_98304_147456 cdem_prefix_assembled_cdemPrefixFastStats_147456_199331
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

lemma cdem_prefix_assembled_cdemPrefixFastStats_0_199331 :
    (∑ n ∈ Ico 0 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 0 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (121174 : ℕ) ∧
    (∑ n ∈ Ico 0 199331, mobiusTreeValue 16 mobiusTable1200001 n*(5000000000/n : ℕ)) = (112 : ℤ) ∧
    (∑ n ∈ Ico 0 199331, mobiusTreeValue 16 mobiusTable1200001 n*(100000000000000000000000000000000/n : ℕ)) = (2098595765597847108232803 : ℤ) := by
  have h := cdem_prefix_assembled_cdem_integer_totals_join
    (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    0 98304 199331 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-76 : ℤ) (70 : ℤ) (-3848609 : ℤ) (3848721 : ℤ) (-76973034169478880966217955323 : ℤ) (76975132765244478813326188126 : ℤ) 59762 61412
    cdem_prefix_assembled_cdemPrefixFastStats_0_98304 cdem_prefix_assembled_cdemPrefixFastStats_98304_199331
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩

theorem cdem_prefix_assembled_cdem_prefix_fast_199330 :
    (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) ∧
    (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 ∧
    (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) ∧
    (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ) ∧
    ((∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) - 1 : ℤ) = 111 ∧
    1 / Real.sqrt (5000000001 : ℝ) ≤
      (14142135622317 / 1000000000000000000 : ℝ) := by
  rcases cdem_prefix_assembled_cdemPrefixFastStats_0_199331 with ⟨hM, hS, hF, hR⟩
  have h := cdem_prefix_assembled_cdem_prefix_of_integer_totals cdem_prefix_assembled_cdemCandidateMu
    cdem_prefix_assembled_cdem_candidate_mu_eq hM hS hF hR
  rcases h with ⟨hM, hS, hF, hL, hU⟩
  exact ⟨hM, hS, hF, hL, hU,
    (congrArg (fun z : ℤ => z-1) hF).trans (by decide),
    cdem_prefix_assembled_cdem_endpoint_reciprocal_sqrt⟩
end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem cdem_prefix_199330_complete :
    (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) ∧
    (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 ∧
    (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) ∧
    (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ) ∧
    ((∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) - 1 : ℤ) = 111 ∧
    1 / Real.sqrt (5000000001 : ℝ) ≤
      (14142135622317 / 1000000000000000000 : ℝ) := cdem_prefix_assembled_cdem_prefix_fast_199330

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution :
    (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) ∧
    (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 ∧
    (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) ∧
    (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ) ∧
    ((∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) - 1 : ℤ) = 111 ∧
    1 / Real.sqrt (5000000001 : ℝ) ≤
      (14142135622317 / 1000000000000000000 : ℝ) := Helfgott.cdem_prefix_199330_complete
#print axioms solution
