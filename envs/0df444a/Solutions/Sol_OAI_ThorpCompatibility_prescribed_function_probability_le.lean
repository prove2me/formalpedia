-- Prove2me | solution 1 for OAI.ThorpCompatibility.prescribed_function_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:46:30.523212+00:00
-- url     : https://prove2.me/submissions/2d7f4320-b454-42db-944f-f5d0c9e57fe3

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/PermutationProbability.lean:L12-L36
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.prescribed_function_probability_le. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_prescribed_function_card_le

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

-- ---- from OAI.Probability.ThorpCompatibility.PermutationProbability ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma prescribed_function_probability_le {α : Type*} [Fintype α] [DecidableEq α]
    (hn : 0 < Fintype.card α) (s : Finset α) (f : α → α) :
    ((Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ (Real.exp 1 / Fintype.card α) ^ s.card := by
  have hs : s.card ≤ Fintype.card α := Finset.card_le_univ s
  have hcard := prescribed_function_card_le s f
  have hfac : (0 : ℝ) < (Fintype.card α).factorial := by positivity
  have hdesc : (0 : ℝ) < (Fintype.card α).descFactorial s.card := by
    exact_mod_cast Nat.descFactorial_pos.mpr hs
  have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have hbase : 0 < ((Fintype.card α : ℝ) / Real.exp 1) ^ s.card := by positivity
  have hmul : ((Fintype.card α - s.card).factorial : ℝ) *
      (Fintype.card α).descFactorial s.card = (Fintype.card α).factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hs
  rw [Fintype.card_perm]
  calc
    _ ≤ ((Fintype.card α - s.card).factorial : ℝ) / (Fintype.card α).factorial :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hfac.le
    _ = 1 / ((Fintype.card α).descFactorial s.card : ℝ) := by
      apply (div_eq_div_iff hfac.ne' hdesc.ne').mpr
      simpa using hmul
    _ ≤ 1 / (((Fintype.card α : ℝ) / Real.exp 1) ^ s.card) :=
      one_div_le_one_div_of_le hbase (descFactorial_exponential_lower _ _ hs)
    _ = (Real.exp 1 / Fintype.card α) ^ s.card := by
      rw [← one_div_pow, one_div_div]

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (hn : 0 < Fintype.card α) (s : Finset α) (f : α → α) :
    ((Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ (Real.exp 1 / Fintype.card α) ^ s.card := by
  first
    | exact OAI.ThorpCompatibility.prescribed_function_probability_le hn s f
    | exact OAI.ThorpCompatibility.prescribed_function_probability_le
    | (apply OAI.ThorpCompatibility.prescribed_function_probability_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.prescribed_function_probability_le <;> assumption)
