-- Prove2me | solution 1 for OAI.ShortEgyptian.prime_prefix_split
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:12:36.896084+00:00
-- url     : https://prove2.me/submissions/35547ae2-2ed7-4f9b-94d3-f0749d5ff85a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeSplitting.lean:L96-L143
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prime_prefix_split. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeSplitting ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_prefix_split {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 1 ≤ R) (hnR : R < n) :
    ∃ d e p : ℕ, n = d*e ∧ d ≠ 0 ∧ e ≠ 0 ∧ p.Prime ∧ p ∣ e ∧
      (d:ℝ) ≤ R ∧ R < (d:ℝ)*p ∧
      (∀ q ∈ d.primeFactorsList, q ≤ p) ∧ (∀ q ∈ e.primeFactorsList, p ≤ q) := by
  induction n using Nat.strong_induction_on generalizing R with
  | h n ih =>
    have hn1 : n ≠ 1 := by intro h; simp [h] at hnR; linarith
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
    by_cases hpR : R < p
    · refine ⟨1,n,p, by simp, by norm_num, hn, hp, Nat.minFac_dvd n, ?_, ?_, ?_, ?_⟩
      · simpa using hR
      · simpa using hpR
      · simp
      · intro q hq
        exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hq).two_le
          (Nat.dvd_of_mem_primeFactorsList hq)
    · have hpR' : (p:ℝ) ≤ R := le_of_not_gt hpR
      let m := n/p
      have hmul : n = p*m := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
      have hm : m ≠ 0 := by intro h; simp [h] at hmul; exact hn hmul
      have hlt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
      have hmR : R / p < (m:ℝ) := by
        apply (div_lt_iff₀ hp0).mpr
        have hh : (n:ℝ) = (p:ℝ)*m := by exact_mod_cast hmul
        nlinarith
      obtain ⟨d,e,q, hde, hd, he, hq, hqe, hdR, hRdp, hdq, heq⟩ :=
        ih m hlt hm (R/p) ((le_div_iff₀ hp0).mpr (by nlinarith)) hmR
      have hpq : p ≤ q := by
        apply Nat.minFac_le_of_dvd hq.two_le
        exact hqe.trans (by rw [hmul,hde]; exact dvd_mul_of_dvd_right (dvd_mul_left e d) p)
      refine ⟨p*d,e,q, ?_, mul_ne_zero hp.ne_zero hd, he, hq, hqe, ?_, ?_, ?_, heq⟩
      · rw [hmul,hde,mul_assoc]
      · have hh := (le_div_iff₀ hp0).mp hdR
        push_cast
        nlinarith
      · have hh := (div_lt_iff₀ hp0).mp hRdp
        push_cast
        nlinarith
      · intro a ha
        have hap := Nat.prime_of_mem_primeFactorsList ha
        have had := Nat.dvd_of_mem_primeFactorsList ha
        rcases hap.dvd_mul.mp had with hah | hah
        · rcases (Nat.dvd_prime hp).mp hah with h1 | h1
          · exact False.elim (hap.ne_one h1)
          · simpa [h1] using hpq
        · exact hdq a ((Nat.mem_primeFactorsList hd).mpr ⟨hap,hah⟩)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prime_prefix_split := @_root_.OAI.ShortEgyptian.prime_prefix_split
