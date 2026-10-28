-- Prove2me | solution 1 for ManneLP.Equilibrium.expected_cost_eq_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:39:05.834013+00:00
-- url     : https://prove2.me/submissions/e9330d9f-f2b2-4cb7-86b6-515095d714a7

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

open ManneLP.Equilibrium in
theorem solution (M : Model)
    (hsum : ∀ a ∈ M.A,
      Summable (fun n : ℕ => M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ))))
    (x : ℕ × ℕ → ℝ) :
    expC₁ M x = ∑ i ∈ states M, marginal M x i * M.C₁ i ∧
      expC₁ M x = ∑ a ∈ M.A, x a * M.C₁ a.1 ∧
      expC₂ M x = ∑ a ∈ M.A, x a * M.C₂ a.2 ∧
      expC₃ M x = ∑ a ∈ M.A, x a * ∑' n : ℕ, M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)) ∧
      expCost M x = lpObj M x := by
  have hp : ∑' n, M.p n = 1 := M.p_hasSum.tsum_eq
  have e1 : expC₁ M x = ∑ a ∈ M.A, x a * M.C₁ a.1 := by
    unfold expC₁
    apply Finset.sum_congr rfl
    intro a _
    have : ∀ n, x a * M.p n * M.C₁ a.1 = (x a * M.C₁ a.1) * M.p n := fun n => by ring
    simp_rw [this]
    rw [tsum_mul_left, hp, mul_one]
  have e2 : expC₂ M x = ∑ a ∈ M.A, x a * M.C₂ a.2 := by
    unfold expC₂
    apply Finset.sum_congr rfl
    intro a _
    have : ∀ n, x a * M.p n * M.C₂ a.2 = (x a * M.C₂ a.2) * M.p n := fun n => by ring
    simp_rw [this]
    rw [tsum_mul_left, hp, mul_one]
  have e3 : expC₃ M x =
      ∑ a ∈ M.A, x a * ∑' n : ℕ, M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)) := by
    unfold expC₃
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
  have e0 : ∑ a ∈ M.A, x a * M.C₁ a.1 = ∑ i ∈ states M, marginal M x i * M.C₁ i := by
    have hsub : M.A ⊆ states M ×ˢ states M := by
      intro a ha
      have := M.A_le a ha
      simp only [states, Finset.mem_product, Finset.mem_range]
      omega
    rw [← Finset.inter_eq_right.mpr hsub, ← Finset.sum_ite_mem, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    unfold marginal actions
    rw [Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  refine ⟨e1.trans e0, e1, e2, e3, ?_⟩
  unfold expCost lpObj costCoeff
  rw [e1, e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring
