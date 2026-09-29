-- Prove2me | solution 1 for NonmonotoneLS.Global.costQ_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:50:10.684281+00:00
-- url     : https://prove2.me/submissions/ad8a0943-0db4-4d56-b248-b7830401879c

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

theorem aux_cqli_nonneg (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax) :
    ∀ k, 0 ≤ Shared.costQ η k := by
  intro k
  induction k with
  | zero => simp [Shared.costQ]
  | succ k ih =>
    simp only [Shared.costQ]
    have := (hη k).1
    positivity

theorem aux_cqli_bound (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax) :
    ∀ k, Shared.costQ η k ≤ 1 + ∑ j ∈ Finset.range k, ηmax ^ (j + 1) := by
  have hm : 0 ≤ ηmax := le_trans (hη 0).1 (hη 0).2
  intro k
  induction k with
  | zero => simp [Shared.costQ]
  | succ k ih =>
    simp only [Shared.costQ]
    have h0 := aux_cqli_nonneg η ηmax hη k
    have h1 : η k * Shared.costQ η k ≤ ηmax * Shared.costQ η k :=
      mul_le_mul_of_nonneg_right (hη k).2 h0
    have h2 : ηmax * Shared.costQ η k ≤ ηmax * (1 + ∑ j ∈ Finset.range k, ηmax ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left ih hm
    have h3 : ηmax * (1 + ∑ j ∈ Finset.range k, ηmax ^ (j + 1)) + 1
        = 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) := by
      rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
      simp only [pow_succ, zero_add, pow_zero, one_mul]
      have : ∀ i ∈ Finset.range k, ηmax * (ηmax ^ i * ηmax) = ηmax ^ i * ηmax * ηmax := by
        intro i _; ring
      rw [Finset.sum_congr rfl this]
      ring
    linarith

end NonmonotoneLS.Global

open NonmonotoneLS.Global
open scoped InnerProductSpace NNReal Topology
open Filter

theorem solution (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) ηmax)
    (hηmax : ηmax < 1) (k : ℕ) :
    NonmonotoneLS.Shared.costQ η (k + 1) ≤ 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ∧
      1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1) ≤ 1 / (1 - ηmax) := by
  refine ⟨aux_cqli_bound η ηmax hη (k + 1), ?_⟩
  have hm : 0 ≤ ηmax := le_trans (hη 0).1 (hη 0).2
  have hpos : 0 < 1 - ηmax := by linarith
  have heq : 1 + ∑ j ∈ Finset.range (k + 1), ηmax ^ (j + 1)
      = ∑ j ∈ Finset.range (k + 2), ηmax ^ j := by
    rw [Finset.sum_range_succ' (fun j => ηmax ^ j) (k + 1)]
    simp only [pow_zero]
    ring
  rw [heq, le_div_iff₀ hpos]
  have hg := mul_neg_geom_sum ηmax (k + 2)
  have hp : 0 ≤ ηmax ^ (k + 2) := pow_nonneg hm _
  rw [mul_comm] at hg
  linarith
