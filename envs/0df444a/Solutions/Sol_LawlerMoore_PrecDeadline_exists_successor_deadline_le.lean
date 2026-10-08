-- Prove2me | solution 1 for LawlerMoore.PrecDeadline.exists_successor_deadline_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:17:12.683961+00:00
-- url     : https://prove2.me/submissions/7004027e-3549-4325-b82f-c91cff50e523

import Mathlib
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline
open LawlerMoore.PrecDeadline

theorem solution (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (i j : Fin n) (hlt : modifiedDeadline ρ d ε j < modifiedDeadline ρ d ε i) :
    ∃ k, (k = j ∨ ρ j k) ∧ d k ≤ d i := by
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_inf'
    (Finset.insert_nonempty j (Finset.univ.filter (ρ j))) d
  refine ⟨k, ?_, ?_⟩
  · simpa only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  · by_contra h
    have hdiff := hgap i k (lt_of_not_ge h)
    have hmin := Finset.inf'_le d (Finset.mem_insert_self i (Finset.univ.filter (ρ i)))
    have hi : (i : ℝ) < (n : ℝ) := by exact_mod_cast i.isLt
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hmul := mul_lt_mul_of_pos_right hi hε
    have hjmul := mul_nonneg hj hε.le
    unfold modifiedDeadline at hlt
    rw [heq] at hlt
    linarith

#print axioms solution
