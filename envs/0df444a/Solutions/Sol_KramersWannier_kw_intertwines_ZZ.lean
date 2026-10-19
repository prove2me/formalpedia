-- Prove2me | solution 1 for KramersWannier.kw_intertwines_ZZ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:00:21.182276+00:00
-- url     : https://prove2.me/submissions/ffb3aa29-8a54-45b4-a97e-bac58d072ef8

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

private lemma phase_add_left {L : ℕ} [NeZero L] (t r s : Config L) :
    phase (t + r) s = phase t s + phase r s := by
  simp only [phase, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma phase_single_left {L : ℕ} [NeZero L] (s : Config L) (j : Fin L) :
    phase (Pi.single j 1) s = s j + s (j + 1) := by
  simp [phase, Pi.single_apply, ite_mul]

private lemma flip_twice {L : ℕ} (s : Config L) (j : Fin L) :
    s + Pi.single j 1 + Pi.single j 1 = s := by
  ext k
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private lemma flip_eq {L : ℕ} (t s : Config L) (j : Fin L) :
    t = s + Pi.single j 1 ↔ s = t + Pi.single j 1 := by
  constructor <;> intro h <;> subst_vars <;> simp only [flip_twice]

end KramersWannier

open KramersWannier

theorem solution (L : ℕ) [NeZero L] (j : Fin L) :
    kwD L * (pauliZ L (j - 1) * pauliZ L j) = pauliX L (j - 1) * kwD L := by
  ext t s
  have hl : (kwD L * (pauliZ L (j - 1) * pauliZ L j)) t s =
      (kwD L t s * sgn (s (j - 1))) * sgn (s j) := by
    rw [← Matrix.mul_assoc]
    simp only [pauliZ, Matrix.mul_diagonal]
  rw [hl]
  simp only [Matrix.mul_apply, pauliX,
    flip_eq t, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  change (kwD L t s * sgn (s (j - 1))) * sgn (s j) =
    kwD L (t + Pi.single (j - 1) 1) s
  change _ = _ * sgn (phase (t + Pi.single (j - 1) 1) s)
  rw [phase_add_left, phase_single_left, sub_add_cancel, sgn_add, sgn_add]
  unfold kwD
  change (_ * sgn (phase t s) * sgn (s (j - 1))) * sgn (s j) = _
  unfold phase
  ring
