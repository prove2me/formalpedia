-- Prove2me | solution 1 for OAI.ThorpCompatibility.log_factorial_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:17:44.698332+00:00
-- url     : https://prove2.me/submissions/66bf6336-09bf-466e-96d0-2555ca9391c3

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/LogEstimates.lean:L41-L56
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.log_factorial_upper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility

-- ---- from OAI.Probability.ThorpCompatibility.LogEstimates ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

lemma log_step_lower {x : ℝ} (hx : 0 < x) :
    Real.log x + 1 ≤ (x + 1) * Real.log (x + 1) - x * Real.log x := by
  have hx1 : 0 < x + 1 := by linarith
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx hx1)) hx1.le
  rw [Real.log_div hx.ne' hx1.ne'] at h
  have hr : (x + 1) * (x / (x + 1) - 1) = -1 := by field_simp; ring
  rw [hr] at h
  nlinarith

lemma log_factorial_upper (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      norm_num
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have h₁ := ih hnpos
    have h₂ := log_step_lower hnreal
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    simp only [Nat.cast_succ]
    linarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  first
    | exact OAI.ThorpCompatibility.log_factorial_upper n hn
    | exact OAI.ThorpCompatibility.log_factorial_upper
    | (apply OAI.ThorpCompatibility.log_factorial_upper <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.log_factorial_upper <;> assumption)
