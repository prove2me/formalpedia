-- Prove2me | solution 1 for KramersWannier.kw_intertwines_X
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:00:18.107277+00:00
-- url     : https://prove2.me/submissions/ac9322d9-598e-4abf-8934-ee7fe89cf82e

import Definitions.Def_KramersWannier_defs

open Matrix
open scoped BigOperators

namespace KramersWannier

private lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [sgn, h]

private def phase {L : ℕ} [NeZero L] (t s : Config L) : ZMod 2 :=
  ∑ k, t k * (s k + s (k + 1))

private lemma phase_add_right {L : ℕ} [NeZero L] (t s r : Config L) :
    phase t (s + r) = phase t s + phase t r := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.add_apply]
  ring

private lemma phase_single_right {L : ℕ} [NeZero L] (t : Config L) (j : Fin L) :
    phase t (Pi.single j 1) = t j + t (j - 1) := by
  simp only [phase, mul_add, Finset.sum_add_distrib, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, ← eq_sub_iff_add_eq]
  simp

end KramersWannier

open KramersWannier

theorem solution (L : ℕ) [NeZero L] (j : Fin L) :
    kwD L * pauliX L j = pauliZ L (j - 1) * pauliZ L j * kwD L := by
  ext t s
  have hr : (pauliZ L (j - 1) * pauliZ L j * kwD L) t s =
      sgn (t (j - 1)) * (sgn (t j) * kwD L t s) := by
    rw [Matrix.mul_assoc]
    simp only [pauliZ, Matrix.diagonal_mul]
  rw [hr]
  simp only [Matrix.mul_apply, pauliX, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  change kwD L t (s + Pi.single j 1) = _
  change _ * sgn (phase t (s + Pi.single j 1)) = _
  rw [phase_add_right, phase_single_right, sgn_add, sgn_add]
  unfold kwD
  unfold phase
  ring
