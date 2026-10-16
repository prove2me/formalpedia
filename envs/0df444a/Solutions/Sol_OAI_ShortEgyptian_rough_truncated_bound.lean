-- Prove2me | solution 1 for OAI.ShortEgyptian.rough_truncated_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:05:19.045367+00:00
-- url     : https://prove2.me/submissions/6a9d7aea-6bf8-4455-bcfe-f27fe3c7a123

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean:L116-L172
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.rough_truncated_bound. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.TruncatedDivisors ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem divisor_generating_prime_mul (q : ℝ) (hq : 0 ≤ q) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    ∑ d ∈ (p*m).divisors, q^(ArithmeticFunction.cardFactors d) ≤
      (1+q) * ∑ d ∈ m.divisors, q^(ArithmeticFunction.cardFactors d) := by
  classical
  let w (d : ℕ) : ℝ := q^(ArithmeticFunction.cardFactors d)
  have hw (d : ℕ) : 0 ≤ w d := pow_nonneg hq _
  have hsub : (p*m).divisors ⊆ m.divisors ∪ m.divisors.image (p*·) := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    apply mem_union.mpr
    by_cases hpd : p ∣ d
    · right
      refine mem_image.mpr ⟨d/p, Nat.mem_divisors.mpr ⟨?_, hm⟩, Nat.mul_div_cancel' hpd⟩
      have hh := Nat.div_dvd_div hpd hdvd
      simpa [Nat.mul_div_cancel_left m hp.pos] using hh
    · left
      exact Nat.mem_divisors.mpr ⟨((hp.coprime_iff_not_dvd.mpr hpd).symm).dvd_of_dvd_mul_left hdvd, hm⟩
  have hsum : (∑ d ∈ m.divisors ∪ m.divisors.image (p*·), w d) ≤
      (∑ d ∈ m.divisors, w d) + ∑ d ∈ m.divisors.image (p*·), w d := by
    have hh := sum_union_inter (s₁ := m.divisors) (s₂ := m.divisors.image (p*·)) (f := w)
    have hnn := sum_nonneg (s := m.divisors ∩ m.divisors.image (p*·)) (fun d _ => hw d)
    linarith
  calc
    _ ≤ ∑ d ∈ m.divisors ∪ m.divisors.image (p*·), w d :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hw d)
    _ ≤ _ := hsum
    _ = (∑ d ∈ m.divisors, w d) + ∑ d ∈ m.divisors, w (p*d) := by
      rw [sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp.pos h)]
    _ = _ := by
      have hmul : ∀ d ∈ m.divisors, w (p*d) = q * w d := by
        intro d hd
        unfold w
        rw [ArithmeticFunction.cardFactors_mul hp.ne_zero (Nat.pos_of_mem_divisors hd).ne',
          ArithmeticFunction.cardFactors_apply_prime hp, pow_add, pow_one]
      rw [sum_congr rfl hmul, ← mul_sum]
      ring

theorem divisor_generating_bound (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, q^(ArithmeticFunction.cardFactors d) ≤
      (1+q)^(ArithmeticFunction.cardFactors n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · simp [hn1]
    have hp := Nat.minFac_prime hn1
    have hm : n / n.minFac ≠ 0 := by
      have hmul := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      intro hz
      simp [hz] at hmul
      exact hn hmul.symm
    have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
    have hmul : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
    calc
      _ = ∑ d ∈ (n.minFac * (n / n.minFac)).divisors, q^(ArithmeticFunction.cardFactors d) := by
        rw [← hmul]
      _ ≤ (1+q) * ∑ d ∈ (n / n.minFac).divisors, q^(ArithmeticFunction.cardFactors d) :=
        divisor_generating_prime_mul q hq hp hm
      _ ≤ (1+q) * (1+q)^(ArithmeticFunction.cardFactors (n / n.minFac)) :=
        mul_le_mul_of_nonneg_left (ih _ hlt hm) (by linarith)
      _ = _ := by
        conv_rhs => rw [hmul]
        rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hm,
          ArithmeticFunction.cardFactors_apply_prime hp, pow_add, pow_one]

theorem rough_truncated_bound {n : ℕ} (hn : n ≠ 0) (X W z q : ℝ)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q < 1)
    (hW : Real.log n ≤ W) (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp ((q * W - Real.log X * Real.log q) / Real.log z) := by
  classical
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hlq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hΩ : (ArithmeticFunction.cardFactors n : ℝ) ≤ W / Real.log z := by
    apply (le_div_iff₀ hlz).mpr
    exact (rough_cardFactors_log hn z (by linarith) hrough).trans hW
  let L := Real.log q * (Real.log X / Real.log z)
  let U := q * W / Real.log z
  have hlower : (truncatedDivisorCount X n : ℝ) * Real.exp L ≤
      ∑ a ∈ truncatedDivisors X n, q^(ArithmeticFunction.cardFactors a) := by
    calc
      _ = ∑ _a ∈ truncatedDivisors X n, Real.exp L := by simp [truncatedDivisorCount]
      _ ≤ _ := by
        apply sum_le_sum
        intro a ha
        have ha' := mem_filter.mp ha
        have had := Nat.mem_divisors.mp ha'.1
        have ha0 : 0 < (a:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors ha'.1
        have hΩa := rough_cardFactors_log (Nat.pos_of_mem_divisors ha'.1).ne' z (by linarith)
          (fun p hp => hrough p (Nat.primeFactorsList_subset_of_dvd had.1 hn hp))
        have hlog := Real.log_le_log ha0 ha'.2
        have hΩa' : (ArithmeticFunction.cardFactors a : ℝ) ≤ Real.log X / Real.log z :=
          (le_div_iff₀ hlz).mpr (hΩa.trans hlog)
        have hmul := mul_le_mul_of_nonpos_left hΩa' hlq.le
        calc
          _ ≤ Real.exp (Real.log q * (ArithmeticFunction.cardFactors a : ℝ)) := Real.exp_le_exp.mpr hmul
          _ = _ := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
  have hupper : (∑ a ∈ n.divisors, q^(ArithmeticFunction.cardFactors a)) ≤ Real.exp U := by
    calc
      _ ≤ (1+q)^(ArithmeticFunction.cardFactors n) := divisor_generating_bound q hq0.le n hn
      _ = Real.exp ((ArithmeticFunction.cardFactors n : ℝ) * Real.log (1+q)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1+q)]
      _ ≤ Real.exp ((ArithmeticFunction.cardFactors n : ℝ) * q) := by
        apply Real.exp_le_exp.mpr
        have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+q)
        gcongr
        linarith
      _ ≤ Real.exp U := by
        apply Real.exp_le_exp.mpr
        dsimp [U]
        calc
          _ = q * (ArithmeticFunction.cardFactors n : ℝ) := mul_comm _ _
          _ ≤ q * (W / Real.log z) := mul_le_mul_of_nonneg_left hΩ hq0.le
          _ = _ := by ring
  have hbound := hlower.trans ((sum_le_sum_of_subset_of_nonneg
    (filter_subset _ _) (fun a _ _ => pow_nonneg hq0.le (ArithmeticFunction.cardFactors a))).trans hupper)
  have heq : Real.exp ((q * W - Real.log X * Real.log q) / Real.log z) * Real.exp L = Real.exp U := by
    rw [← Real.exp_add]
    congr 1
    dsimp [L,U]
    ring
  nlinarith [Real.exp_pos L]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.rough_truncated_bound := @_root_.OAI.ShortEgyptian.rough_truncated_bound
