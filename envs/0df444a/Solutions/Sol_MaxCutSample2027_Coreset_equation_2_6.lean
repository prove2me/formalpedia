-- Prove2me | solution 1 for MaxCutSample2027.Coreset.equation_2_6
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:50:06.611751+00:00
-- url     : https://prove2.me/submissions/837e2a3a-634e-417f-a07e-58cab6ffd0ee

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (_hA : IsWeightMatrix A) (_hp : IsPositiveProbabilityVector p)
    (q c : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    M (K A p) q c = ∑ v, q v * max ((∑ u, K A p v u * c u)) 0 := by
  classical
  let score (v : V) := ∑ u, K A p v u * c u
  let a (v : V) := if 0 ≤ score v then q v else 0
  have ha : a ∈ Z q := by
    intro v
    dsimp [a]
    split_ifs
    · exact ⟨hq v, le_rfl⟩
    · exact ⟨le_rfl, hq v⟩
  have value (b : V → ℝ) : bilinear (K A p) b c = ∑ v, b v * score v := by
    unfold bilinear
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  have upper (b : V → ℝ) (hb : b ∈ Z q) : bilinear (K A p) b c ≤ ∑ v, q v * max (score v) 0 := by
    rw [value]
    apply Finset.sum_le_sum
    intro v _
    by_cases h : 0 ≤ score v
    · rw [max_eq_left h]
      exact mul_le_mul_of_nonneg_right (hb v).2 h
    · rw [max_eq_right (le_of_not_ge h), mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (hb v).1 (le_of_not_ge h)
  have attained : bilinear (K A p) a c = ∑ v, q v * max (score v) 0 := by
    rw [value]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : 0 ≤ score v
    · simp [a, h]
    · simp [a, h, max_eq_right (le_of_not_ge h)]
  unfold M
  refine le_antisymm (csSup_le ⟨_, ⟨a, ha, rfl⟩⟩ ?_) ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact upper b hb
  · rw [← attained]
    exact le_csSup ⟨_, by rintro _ ⟨b, hb, rfl⟩; exact upper b hb⟩ ⟨a, ha, rfl⟩
