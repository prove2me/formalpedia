-- Prove2me | solution 1 for KramersWannier.kw_absorbs_eta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:53:50.730487+00:00
-- url     : https://prove2.me/submissions/3b1dfe88-b612-4893-b3c0-d9080d5b5bb0

import Definitions.Def_KramersWannier_defs

open Matrix
open scoped BigOperators

namespace KramersWannier

private lemma flip_twice {L : ℕ} (s : Config L) : s + 1 + 1 = s := by
  ext j
  change s j + 1 + 1 = s j
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  rw [add_assoc, h, add_zero]

private lemma flip_eq {L : ℕ} (t s : Config L) : t = s + 1 ↔ s = t + 1 := by
  constructor <;> intro h <;> subst_vars <;> simp only [flip_twice]

private lemma kw_flip_right (L : ℕ) [NeZero L] (t s : Config L) :
    kwD L t (s + 1) = kwD L t s := by
  unfold kwD
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  change t k * ((s k + 1) + (s (k + 1) + 1)) = _
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  congr 1
  linear_combination h

private lemma kw_flip_left (L : ℕ) [NeZero L] (t s : Config L) :
    kwD L (t + 1) s = kwD L t s := by
  have hs : (∑ k : Fin L, s (k + 1)) = ∑ k : Fin L, s k := by
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin L)) s
  have hsum : (∑ k : Fin L, (s k + s (k + 1))) = 0 := by
    rw [Finset.sum_add_distrib, hs]
    exact CharTwo.add_self_eq_zero _
  unfold kwD
  congr 2
  calc
    ∑ k : Fin L, (t + 1) k * (s k + s (k + 1)) =
        (∑ k : Fin L, t k * (s k + s (k + 1))) +
        ∑ k : Fin L, (s k + s (k + 1)) := by
      simp only [Pi.add_apply, Pi.one_apply, add_mul, one_mul, Finset.sum_add_distrib]
    _ = _ := by rw [hsum, add_zero]

end KramersWannier

open KramersWannier

theorem solution (L : ℕ) [NeZero L] :
    kwD L * eta L = kwD L ∧ eta L * kwD L = kwD L := by
  constructor
  · ext t s
    simp only [Matrix.mul_apply, eta]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    exact kw_flip_right L t s
  · ext t s
    simp only [Matrix.mul_apply, eta]
    simp only [flip_eq t, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    exact kw_flip_left L t s
