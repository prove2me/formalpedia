-- Prove2me | solution 1 for NieYangPareto.supporting_normal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:33:56.36621+00:00
-- url     : https://prove2.me/submissions/823414b4-2053-41c4-8784-46e99cdc61cf

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_U

open NieYangPareto in
theorem solution {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (w : Fin m → ℝ) (b : ℝ) (hw : w ≠ 0)
    (hb : IsGLB ((fun u => w ⬝ᵥ u) '' P.U) b) :
    0 ≤ w := by
  intro i
  change (0 : ℝ) ≤ w i
  by_contra hneg
  push_neg at hneg
  have hU : P.U.Nonempty := by
    by_contra hU
    rw [Set.not_nonempty_iff_eq_empty] at hU
    rw [hU, Set.image_empty] at hb
    have := hb.2 (show b + 1 ∈ lowerBounds (∅ : Set ℝ) by simp)
    linarith
  obtain ⟨u, x, hxK, hx⟩ := hU
  have hbu : b ≤ w ⬝ᵥ u := hb.1 ⟨u, ⟨x, hxK, hx⟩, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (w ⬝ᵥ u - b + 1) / (-w i) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; apply div_nonneg <;> linarith
  let v : Fin m → ℝ := fun k => u k + if k = i then t else 0
  have hv : v ∈ P.U := ⟨x, hxK, fun k => le_trans (hx k) (by
    show u k ≤ u k + if k = i then t else 0
    split_ifs <;> linarith)⟩
  have hdot : w ⬝ᵥ v = w ⬝ᵥ u + w i * t := by
    simp only [v, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hbv : b ≤ w ⬝ᵥ v := hb.1 ⟨v, hv, rfl⟩
  have hwt : w i * t = -(w ⬝ᵥ u - b + 1) := by
    rw [ht, mul_div_assoc']
    rw [div_eq_iff (ne_of_gt (by linarith))]
    ring
  linarith
