-- Prove2me | solution 1 for OAI.ThorpCompatibility.clump_exp_moment_simple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:53:56.27671+00:00
-- url     : https://prove2.me/submissions/d4702b41-8901-4d2d-a71c-4dae08c4ef7a

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/MomentBound.lean:L10-L36
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.clump_exp_moment_simple. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Theorems.Thm_OAI_ThorpCompatibility_clump_exp_moment_le
import Theorems.Thm_OAI_ThorpCompatibility_clump_subset_sum

-- ---- from OAI.Probability.ThorpCompatibility.FactorialBounds ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma log_step_bound (n : ℕ) :
    ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) * Real.log n ≤
      Real.log ((n : ℝ) + 1) + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hn1 hn0)) hn0.le
  rw [Real.log_div hn1.ne' hn0.ne'] at h
  have hr : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp
    ring
  rw [hr] at h
  nlinarith

lemma log_descFactorial_integral (n k : ℕ) (hk : k ≤ n) :
    (n : ℝ) * Real.log n - (n - k : ℕ) * Real.log (n - k : ℕ) - k ≤
      Real.log (n.descFactorial k : ℝ) := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
      have h₁ := ih k hk'
      have h₂ := log_step_bound n
      have hd : (n.descFactorial k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.descFactorial_pos.mpr hk').ne'
      rw [Nat.succ_descFactorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) hd]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_succ] at *
      linarith

lemma log_descFactorial_lower (n k : ℕ) (hk : k ≤ n) :
    (k : ℝ) * (Real.log n - 1) ≤ Real.log (n.descFactorial k : ℝ) := by
  have h := log_descFactorial_integral n k hk
  have hnk : (n - k : ℕ) * Real.log (n - k : ℕ) ≤
      (n - k : ℕ) * Real.log n := by
    by_cases hz : n - k = 0
    · simp [hz]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
    exact_mod_cast Nat.sub_le n k
  rw [Nat.cast_sub hk] at h hnk
  nlinarith

lemma descFactorial_exponential_lower (n k : ℕ) (hk : k ≤ n) :
    ((n : ℝ) / Real.exp 1) ^ k ≤ (n.descFactorial k : ℝ) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (Nat.pos_of_ne_zero hk0) hk
  have hd : (0 : ℝ) < n.descFactorial k := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk
  apply (Real.log_le_log_iff (pow_pos (div_pos hn0 (Real.exp_pos _)) _) hd).mp
  rw [Real.log_pow, Real.log_div hn0.ne' (Real.exp_ne_zero _), Real.log_exp]
  exact log_descFactorial_lower n k hk

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ClumpMoments ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma clumpWeight_nonneg {α : Type*} (H z : ℝ) (s : Finset α) :
    0 ≤ clumpWeight H z s := by
  unfold clumpWeight
  split_ifs <;> positivity

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.BinomialBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma choose_poisson_bound (a h : ℕ) (hh : 0 < h) (t : ℝ) (ht : 0 ≤ t) :
    (a.choose h : ℝ) * t ^ h ≤ (Real.exp 1 * a * t / h) ^ h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hbase : 0 < ((h : ℝ) / Real.exp 1) ^ h := by positivity
  have hf := descFactorial_exponential_lower h h (le_refl h)
  rw [Nat.descFactorial_self] at hf
  calc
    _ ≤ ((a : ℝ) ^ h / h.factorial) * t ^ h :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div h a) (pow_nonneg ht _)
    _ ≤ ((a : ℝ) ^ h / ((h : ℝ) / Real.exp 1) ^ h) * t ^ h := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht _)
      exact div_le_div_of_nonneg_left (by positivity) hbase hf
    _ = _ := by
      rw [← div_pow, ← mul_pow]
      congr 1
      field_simp

lemma binomial_large_size_term (a h : ℕ) (H t : ℝ) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hsmall : Real.exp 2 * a * t ≤ H) (hh : H < h) :
    (a.choose h : ℝ) * t ^ h ≤ Real.exp (-H) := by
  have hh' : (0 : ℝ) < h := lt_of_le_of_lt hH hh
  have hhN : 0 < h := by exact_mod_cast hh'
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hbase : Real.exp 1 * a * t / h ≤ 1 / Real.exp 1 := by
    apply (div_le_div_iff₀ hh' (Real.exp_pos _)).mpr
    rw [he] at hsmall
    nlinarith
  calc
    _ ≤ (Real.exp 1 * a * t / h) ^ h := choose_poisson_bound a h hhN t ht
    _ ≤ (1 / Real.exp 1) ^ h := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp (-(h : ℝ)) := by
      rw [one_div, ← Real.exp_neg, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-H) := Real.exp_le_exp.mpr (neg_le_neg hh.le)

lemma binomial_large_size_sum (a : ℕ) (H t : ℝ) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hsmall : Real.exp 2 * a * t ≤ H) :
    (∑ h ∈ Finset.range (a + 1),
      if h = 0 then (1 : ℝ) else if H < h then (a.choose h : ℝ) * t ^ h else 0) ≤
        1 + (a + 1 : ℕ) * Real.exp (-H) := by
  calc
    _ ≤ ∑ h ∈ Finset.range (a + 1), ((if h = 0 then (1 : ℝ) else 0) + Real.exp (-H)) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hz : h = 0
      · simp [hz, (Real.exp_pos (-H)).le]
      · by_cases hh : H < h
        · simpa [hz, hh] using binomial_large_size_term a h H t hH ht hsmall hh
        · simp [hz, hh, (Real.exp_pos (-H)).le]
    _ = _ := by simp [Finset.sum_add_distrib]

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.MomentBound ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma clump_exp_moment_simple {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β)
    (hsmall : Real.exp 2 * Fintype.card α *
      (Real.exp z * (Real.exp 1 / Fintype.card β)) ≤ H) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      Real.exp ((Fintype.card β : ℝ) ^ 2 * (Fintype.card α + 1) * Real.exp (-H)) := by
  have hbin := binomial_large_size_sum (Fintype.card α) H
    (Real.exp z * (Real.exp 1 / Fintype.card β)) hH (by positivity) hsmall
  have hsum : (∑ s : Finset α, clumpWeight H z s *
      (Real.exp 1 / Fintype.card β) ^ s.card) ≤
        1 + (Fintype.card α + 1 : ℕ) * Real.exp (-H) := by
    rw [clump_subset_sum]
    exact hbin
  calc
    _ ≤ _ := clump_exp_moment_le H z hH hn
    _ ≤ (1 + (Fintype.card α + 1 : ℕ) * Real.exp (-H)) ^ (Fintype.card β ^ 2) := by
      apply pow_le_pow_left₀ _ hsum
      exact Finset.sum_nonneg fun s _ => mul_nonneg (clumpWeight_nonneg _ _ _) (by positivity)
    _ ≤ (Real.exp ((Fintype.card α + 1 : ℕ) * Real.exp (-H))) ^ (Fintype.card β ^ 2) := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using
        Real.add_one_le_exp ((Fintype.card α + 1 : ℕ) * Real.exp (-H))
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β)
    (hsmall : Real.exp 2 * Fintype.card α *
      (Real.exp z * (Real.exp 1 / Fintype.card β)) ≤ H) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      Real.exp ((Fintype.card β : ℝ) ^ 2 * (Fintype.card α + 1) * Real.exp (-H)) := by
  first
    | exact OAI.ThorpCompatibility.clump_exp_moment_simple H z hH hn hsmall
    | exact OAI.ThorpCompatibility.clump_exp_moment_simple
    | (apply OAI.ThorpCompatibility.clump_exp_moment_simple <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.clump_exp_moment_simple <;> assumption)
