-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:13:51.679358+00:00
-- url     : https://prove2.me/submissions/ee6e6b1d-b4fb-46f8-9dde-4bc03be976a2

import Mathlib
import Definitions.Def_MetricEntropyDuality
import Theorems.Thm_OAI_MetricEntropyDuality_exists_entropy_pair_with_budget

open OAI OAI.MetricEntropyDuality
open scoped BigOperators Pointwise

theorem solution
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ) := by
  set H : ℝ := 2 * (compressionRadius a : ℝ) ^ 2 * (pivotSlots (accuracy a) : ℝ) with hH
  have hH0 : 0 ≤ H := by positivity
  set r : ℕ := Nat.ceil (4 * b * H) + 1 with hr
  have hr1 : 1 ≤ r := by omega
  have hB : (0:ℝ) < 4 * b := by linarith
  obtain ⟨E⟩ := exists_entropy_pair_with_budget a ha r hr1 (4 * b) hB
  refine ⟨E.dimension, E.dimension_pos, E.body, E.body_isSymmetricConvexBody, E.primal_coverable,
    E.dual_coverable, ?_⟩
  have hbud : entropyBudget a r (4 * b) ≤ 1 / b := by
    unfold entropyBudget
    have hrr : (4 * b * H) + 1 ≤ (r : ℝ) + (compressionRadius a : ℝ) - 1 := by
      have h1 := Nat.le_ceil (4 * b * H)
      have h2 : (1:ℝ) ≤ compressionRadius a := by
        have : 1 ≤ compressionRadius a := by unfold compressionRadius; omega
        exact_mod_cast this
      have : (r : ℝ) = (Nat.ceil (4 * b * H) : ℝ) + 1 := by rw [hr]; push_cast; ring
      linarith
    have hpos : 0 < (r : ℝ) + (compressionRadius a : ℝ) - 1 := by nlinarith
    have hfirst : H / ((r : ℝ) + (compressionRadius a : ℝ) - 1) ≤ 1 / (4 * b) := by
      rw [div_le_div_iff₀ hpos hB]; nlinarith
    rw [← hH]
    calc H / ((r : ℝ) + (compressionRadius a : ℝ) - 1) + 2 / (4 * b)
        ≤ 1 / (4 * b) + 2 / (4 * b) := by linarith
      _ ≤ 1 / b := by
          have hb0 : 0 < b := by linarith
          rw [show 1 / (4 * b) + 2 / (4 * b) = (3/4) * (1 / b) by field_simp; ring]
          have : 0 < 1 / b := by positivity
          linarith
  have hratio := E.ratio_lt
  have hlog := E.primal_log_pos
  unfold entropyRatio at hratio
  have hlt : Real.log (coveringNumber (polar (cube (Fin E.dimension))) (a⁻¹ • polar E.body) : ℝ) <
      Real.log (coveringNumber E.body (cube (Fin E.dimension)) : ℝ) * (1 / b) := by
    rw [← div_lt_iff₀' hlog] ; linarith
  have hb0 : 0 < b := by linarith
  calc b * Real.log (coveringNumber (polar (cube (Fin E.dimension))) (a⁻¹ • polar E.body) : ℝ)
      < b * (Real.log (coveringNumber E.body (cube (Fin E.dimension)) : ℝ) * (1 / b)) :=
        mul_lt_mul_of_pos_left hlt hb0
    _ = _ := by field_simp
