-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:39:49.811699+00:00
-- url     : https://prove2.me/submissions/1a2f1da5-6a5f-43db-a4c0-ea892e443b39

import Theorems.Thm_NestedLogitVariants_PartialCompetitive_nest_max_eq_knapsack_max
import Theorems.Thm_NestedLogitVariants_PartialCompetitive_xh_nonneg
import Theorems.Thm_NestedLogitVariants_PartialCompetitive_ineq_28
import Theorems.Thm_NestedLogitVariants_PartialCompetitive_ineq_29

open NestedLogitVariants.PartialCompetitive
open Finset

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh) :
    LP3Feasible I (2 * xh) (2 • yh) := by
  classical
  constructor
  · simp only [Pi.smul_apply, two_smul, ← two_mul]
    change (∑ i, 2 * yh i) ≤ I.v0 * (2 * xh)
    rw [← mul_sum]
    nlinarith [hopt.1.1]
  · intro i S
    simp only [Pi.smul_apply, two_smul, ← two_mul]
    change nestWeight I i S * (R I i S - 2 * xh) ≤ 2 * yh i
    by_cases hn : 0 < n
    · have hx := xh_nonneg I hI hγ hn xh yh hopt
      apply (nest_max_eq_knapsack_max I hI hγ i (2 * xh) (by positivity) (2 * yh i)).mpr _ S
      intro ε hε
      by_cases hf : ∃ k, zhat I i ε k ∈ Set.Ioo (0 : ℝ) 1
      · obtain ⟨k, hk⟩ := hf
        exact ineq_28 I hI hγ hn xh yh hopt i ε hε k hk
      · exact ineq_29 I hI hγ hn xh yh hopt i ε hε (fun k hk => hf ⟨k, hk⟩)
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      have hS : S = Shat I i 0 := Subsingleton.elim _ _
      have h := hopt.1.2 i S (Or.inl ⟨0, le_refl _, hS⟩)
      have he : S = ∅ := Subsingleton.elim _ _
      have hr : R I i S = 0 := by simp [R, he]
      rw [hr] at h ⊢
      nlinarith

#print axioms solution
