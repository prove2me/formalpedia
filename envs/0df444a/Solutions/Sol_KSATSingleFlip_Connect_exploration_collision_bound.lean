-- Prove2me | solution 1 for KSATSingleFlip.Connect.exploration_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:09:17.674222+00:00
-- url     : https://prove2.me/submissions/69de4a43-99dd-43c2-aba9-ae695d383bce

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution {Ω : Type} [Fintype Ω] (m n : ℕ) (hn : 0 < n)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Fin m → Ω → Fin n)
    (hpair : ∀ i j : Fin m, i ≠ j → (∑ ω, if X i ω = X j ω then p ω else 0) ≤ 1/(n:ℝ)) :
    (∑ ω, if ∃ i j : Fin m, i ≠ j ∧ X i ω = X j ω then p ω else 0) ≤
      (m:ℝ)^2/(n:ℝ) := by
  classical
  let G : Fin m → Fin m → Ω → ℝ := fun i j ω => if i ≠ j ∧ X i ω = X j ω then p ω else 0
  have hG (i j : Fin m) (ω : Ω) : 0 ≤ G i j ω := by dsimp [G]; split_ifs <;> simp [hp]
  have hpoint (ω : Ω) : (if ∃ i j : Fin m, i ≠ j ∧ X i ω = X j ω then p ω else 0) ≤
      ∑ i : Fin m, ∑ j : Fin m, G i j ω := by
    split_ifs with he
    · obtain ⟨i,j,hij,hx⟩ := he
      have hrow : G i j ω ≤ ∑ j' : Fin m, G i j' ω := Finset.single_le_sum (fun j' _ => hG i j' ω) (Finset.mem_univ j)
      have hcol : (∑ j' : Fin m, G i j' ω) ≤ ∑ i' : Fin m, ∑ j' : Fin m, G i' j' ω :=
        Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => hG i' j' ω)) (Finset.mem_univ i)
      simpa [G,hij,hx] using hrow.trans hcol
    · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hG i j ω))
  have hpair' (i j : Fin m) : (∑ ω, G i j ω) ≤ 1/(n:ℝ) := by
    by_cases hij : i=j
    · subst j
      simp only [G, ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero]
      positivity
    · simpa [G,hij] using hpair i j hij
  calc
    (∑ ω, if ∃ i j : Fin m, i ≠ j ∧ X i ω = X j ω then p ω else 0) ≤
        ∑ ω, ∑ i : Fin m, ∑ j : Fin m, G i j ω := Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = ∑ i : Fin m, ∑ j : Fin m, ∑ ω, G i j ω := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, (1/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (fun j _ => hpair' i j)
    _ = (m:ℝ)^2/(n:ℝ) := by simp [pow_two]; ring
