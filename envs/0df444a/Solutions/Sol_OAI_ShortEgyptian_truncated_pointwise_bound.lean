-- Prove2me | solution 1 for OAI.ShortEgyptian.truncated_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:09:01.425226+00:00
-- url     : https://prove2.me/submissions/4e6f9db4-d466-4a65-8780-d2a7e33db061

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeSplitting.lean:L77-L94
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.truncated_pointwise_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Theorems.Thm_OAI_ShortEgyptian_rough_cardFactors_log
import Theorems.Thm_OAI_ShortEgyptian_rough_truncated_bound
import Theorems.Thm_OAI_ShortEgyptian_truncatedDivisors_mul

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeSplitting ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem small_prime_divisor_bound {n : ℕ} (hn : n ≠ 0) (z W : ℝ)
    (hz : 0 ≤ z) (hW : Real.log n ≤ W)
    (hsmooth : ∀ p ∈ n.primeFactorsList, (p:ℝ) ≤ z) :
    (n.divisors.card : ℝ) ≤ Real.exp (z * Real.log (1+W/Real.log 2)) := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΩ : (ArithmeticFunction.cardFactors n : ℝ) ≤ W / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    exact (rough_cardFactors_log hn 2 (by norm_num) (fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).two_le)).trans hW
  have hΩ0 : 0 ≤ W/Real.log 2 := le_trans (Nat.cast_nonneg _) hΩ
  have hfac (p : ℕ) : n.factorization p ≤ ArithmeticFunction.cardFactors n := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    simpa using (Finsupp.single_le_sum n.factorization (g := fun _ k => k) (fun _ k => Nat.zero_le k) p)
  have hcard : (n.primeFactors.card:ℝ) ≤ z := by
    have hsub : n.primeFactors ⊆ Icc 1 ⌊z⌋₊ := by
      intro p hp
      have hh := Nat.mem_primeFactors.mp hp
      exact mem_Icc.mpr ⟨hh.1.one_lt.le, Nat.le_floor (hsmooth p ((Nat.mem_primeFactorsList hn).mpr ⟨hh.1,hh.2.1⟩))⟩
    have hhh := card_le_card hsub
    have hc : n.primeFactors.card ≤ ⌊z⌋₊ := by simpa using hhh
    exact le_trans (by exact_mod_cast hc) (Nat.floor_le hz)
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p:ℝ)+1) := by rw [Nat.card_divisors hn, Nat.cast_prod]; simp
    _ ≤ (1+W/Real.log 2)^n.primeFactors.card := by
      calc
        _ ≤ ∏ _p ∈ n.primeFactors, (1+W/Real.log 2) := by
          apply prod_le_prod (fun p _ => by positivity)
          intro p _
          have hh : (n.factorization p:ℝ) ≤ ArithmeticFunction.cardFactors n := by exact_mod_cast hfac p
          linarith
        _ = _ := by simp
    _ = Real.exp ((n.primeFactors.card:ℝ)*Real.log (1+W/Real.log 2)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by linarith)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hcard (Real.log_nonneg (by linarith))

theorem prime_threshold_split {n : ℕ} (hn : n ≠ 0) (z : ℝ) :
    ∃ d e : ℕ, n = d*e ∧ d ≠ 0 ∧ e ≠ 0 ∧
      (∀ p ∈ d.primeFactorsList, (p:ℝ) ≤ z) ∧
      (∀ p ∈ e.primeFactorsList, z ≤ p) := by
  classical
  let l := n.primeFactorsList
  let f (p : ℕ) : Bool := decide ((p:ℝ) < z)
  let d := (l.filter f).prod
  let e := (l.filter (fun p => !f p)).prod
  have hde : n = d*e := by
    have hh := (List.filter_append_perm f l).prod_eq
    rw [List.prod_append, Nat.prod_primeFactorsList hn] at hh
    exact hh.symm
  have hd : d ≠ 0 := by intro hh; simp [hh] at hde; exact hn hde
  have he : e ≠ 0 := by intro hh; simp [hh] at hde; exact hn hde
  refine ⟨d,e,hde,hd,he,?_,?_⟩
  · intro p hp
    have hh := mem_list_primes_of_dvd_prod (Nat.prime_of_mem_primeFactorsList hp).prime
      (L := l.filter f) (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime)
      (Nat.dvd_of_mem_primeFactorsList hp)
    have hlt : (p:ℝ) < z := by simpa [f] using (List.mem_filter.mp hh).2
    exact hlt.le
  · intro p hp
    have hh := mem_list_primes_of_dvd_prod (Nat.prime_of_mem_primeFactorsList hp).prime
      (L := l.filter (fun q => !f q)) (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime)
      (Nat.dvd_of_mem_primeFactorsList hp)
    have hlt : ¬ (p:ℝ) < z := by simpa [f] using (List.mem_filter.mp hh).2
    exact le_of_not_gt hlt

theorem truncated_pointwise_bound {n : ℕ} (hn : n ≠ 0) (X W z q : ℝ)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q < 1) (hW : Real.log n ≤ W) :
    (truncatedDivisorCount X n:ℝ) ≤ Real.exp
      (z * Real.log (1+W/Real.log 2) + (q*W-Real.log X*Real.log q)/Real.log z) := by
  obtain ⟨d,e,hde,hd,he,hs,hr⟩ := prime_threshold_split hn z
  have hdle : (d:ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hde ▸ dvd_mul_right d e)
  have hele : (e:ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hde ▸ dvd_mul_left e d)
  have hdW := (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hd) hdle).trans hW
  have heW := (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero he) hele).trans hW
  have hm : (truncatedDivisorCount X n:ℝ) ≤ (d.divisors.card:ℝ)*truncatedDivisorCount X e := by
    exact_mod_cast (hde ▸ truncatedDivisors_mul X hd he)
  calc
    _ ≤ _ := hm
    _ ≤ Real.exp (z * Real.log (1+W/Real.log 2)) *
          Real.exp ((q*W-Real.log X*Real.log q)/Real.log z) :=
      mul_le_mul (small_prime_divisor_bound hd z W (by linarith) hdW hs)
        (rough_truncated_bound he X W z q hz hq0 hq1 heW hr) (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.truncated_pointwise_bound := @_root_.OAI.ShortEgyptian.truncated_pointwise_bound
