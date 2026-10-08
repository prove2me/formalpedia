-- Prove2me | solution 1 for OAI.Erdos3.prepared_source_side_budgets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:21:46.931347+00:00
-- url     : https://prove2.me/submissions/283203a5-96f2-4929-b3fa-dc1680848bb1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Theorems.Thm_OAI_Erdos3_prepared_source_cost_add_required

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSourceSideBudget
namespace OAI

section

namespace Erdos3

theorem prepared_slice_length_fraction {cost N length : ℝ}
    (hloss : N ≤ Real.exp cost * length) :
    Real.exp (-cost) * N ≤ length := by
  calc
    _ ≤ Real.exp (-cost) * (Real.exp cost * length) :=
      mul_le_mul_of_nonneg_left hloss (Real.exp_nonneg _)
    _ = length := by rw [← mul_assoc, ← Real.exp_add]; simp

theorem prepared_source_side_budget {p required N length : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e)
    (hlarge : Real.exp ((p + 2) ^ (max c e + 1)) ≤ N)
    (hloss : N ≤ Real.exp ((p + 2) ^ c) * length) :
    Real.exp required ≤ length ∧
      Real.exp (-((p + 2) ^ c)) * N ≤ length := by
  refine ⟨?_, prepared_slice_length_fraction hloss⟩
  apply le_of_mul_le_mul_left _ (Real.exp_pos ((p + 2) ^ c))
  calc
    Real.exp ((p + 2) ^ c) * Real.exp required =
        Real.exp ((p + 2) ^ c + required) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (max c e + 1)) :=
      Real.exp_le_exp.mpr (prepared_source_cost_add_required hp hrequired)
    _ ≤ N := hlarge
    _ ≤ Real.exp ((p + 2) ^ c) * length := hloss

theorem prepared_source_side_budgets {X : Type*} {p required : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e)
    (N length : X → ℕ)
    (hlarge : ∀ i, Real.exp ((p + 2) ^ (max c e + 1)) ≤ N i)
    (hloss : ∀ i, (N i : ℝ) ≤ Real.exp ((p + 2) ^ c) * length i) :
    (∀ i, Real.exp required ≤ (length i : ℝ)) ∧
      (∀ i, Real.exp (-((p + 2) ^ c)) * N i ≤ (length i : ℝ)) := by
  have h i := prepared_source_side_budget hp hrequired (hlarge i) (hloss i)
  exact ⟨fun i => (h i).1, fun i => (h i).2⟩

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.prepared_source_side_budgets.{u_1} := @OAI.Erdos3.prepared_source_side_budgets.{u_1}
