-- Prove2me | solution 1 for NonmonotoneLS.Global.costQ_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:57:23.29581+00:00
-- url     : https://prove2.me/submissions/9f959c61-4bec-4fd9-95e5-8a1680e5f8ff

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

theorem aux_cqcf_bounds (η : ℕ → ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ Shared.costQ η k ∧ Shared.costQ η k ≤ (k : ℝ) + 1 := by
  induction k with
  | zero => simp [Shared.costQ]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := hη k
    obtain ⟨ih0, ih1⟩ := ih
    simp only [Shared.costQ]
    push_cast
    constructor
    · have := mul_nonneg h0 ih0
      linarith
    · have : η k * Shared.costQ η k ≤ 1 * Shared.costQ η k :=
        mul_le_mul_of_nonneg_right h1 ih0
      linarith

theorem aux_cqcf_step (η : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1 + 1), ∏ m ∈ Finset.range (i + 1), η (j + 1 - m) =
      η (j + 1) * (1 + ∑ i ∈ Finset.range (j + 1), ∏ m ∈ Finset.range (i + 1), η (j - m)) := by
  rw [Finset.sum_range_succ', mul_add, mul_one, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.prod_range_succ' _ (i + 1), mul_comm]
    simp [Nat.add_sub_add_right]

theorem aux_cqcf_formula (η : ℕ → ℝ) (j : ℕ) :
    Shared.costQ η (j + 1) =
        1 + ∑ i ∈ Finset.range (j + 1), ∏ m ∈ Finset.range (i + 1), η (j - m) := by
  induction j with
  | zero => simp [Shared.costQ]; ring
  | succ j ih =>
    rw [Shared.costQ, ih, aux_cqcf_step]
    ring

end NonmonotoneLS.Global

open NonmonotoneLS.Global
open scoped InnerProductSpace NNReal Topology
open Filter

theorem solution (η : ℕ → ℝ) (hη : ∀ k, η k ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    NonmonotoneLS.Shared.costQ η (j + 1) =
        1 + ∑ i ∈ Finset.range (j + 1), ∏ m ∈ Finset.range (i + 1), η (j - m) ∧
      NonmonotoneLS.Shared.costQ η (j + 1) ≤ (j : ℝ) + 2 := by
  refine ⟨aux_cqcf_formula η j, ?_⟩
  have := (aux_cqcf_bounds η hη (j + 1)).2
  push_cast at this
  linarith
