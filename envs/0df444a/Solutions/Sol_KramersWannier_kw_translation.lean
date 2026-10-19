-- Prove2me | solution 1 for KramersWannier.kw_translation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:07:48.147881+00:00
-- url     : https://prove2.me/submissions/9408f1b3-a5f2-451b-8eb9-e3f15d6aa3d9

import Definitions.Def_KramersWannier_defs

open Matrix
open scoped BigOperators

namespace KramersWannier

private lemma shift_eq {L : ℕ} [NeZero L] (t s : Config L) :
    t = (fun k => s (k - 1)) ↔ s = (fun k => t (k + 1)) := by
  constructor <;> intro h <;> subst_vars <;> ext k <;> simp

private lemma transl_mul {L : ℕ} [NeZero L] (A : Op L) (t s : Config L) :
    (transl L * A) t s = A (fun k => t (k + 1)) s := by
  simp only [Matrix.mul_apply, transl, shift_eq t, ite_mul, one_mul, zero_mul]
  simp

private lemma mul_transl {L : ℕ} [NeZero L] (A : Op L) (t s : Config L) :
    (A * transl L) t s = A t (fun k => s (k - 1)) := by
  simp [Matrix.mul_apply, transl]

private lemma phase_shift {L : ℕ} [NeZero L] (t s : Config L) :
    (∑ k, t (k + 1) * (s k + s (k + 1))) =
      ∑ k, t k * (s (k - 1) + s k) := by
  simpa using (Equiv.sum_comp (Equiv.addRight (1 : Fin L))
    (fun k => t k * (s (k - 1) + s k)))

private lemma phase_swap {L : ℕ} [NeZero L] (t s : Config L) :
    (∑ k, s k * (t k + t (k + 1))) =
      ∑ k, t k * (s (k - 1) + s k) := by
  have h := Equiv.sum_comp (Equiv.addRight (1 : Fin L))
    (fun k => t k * s (k - 1))
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
  simp only [mul_add, Finset.sum_add_distrib]
  simpa only [mul_comm] using congrArg (fun a => (∑ k, t k * s k) + a) h |>.trans (add_comm _ _)

private lemma star_sgn (a : ZMod 2) : star (sgn a) = sgn a := by
  unfold sgn
  split <;> simp

end KramersWannier

open KramersWannier

theorem solution (L : ℕ) [NeZero L] :
    transl L * kwD L = kwD L * transl L ∧ (kwD L)ᴴ = kwD L * transl L := by
  constructor
  · ext t s
    rw [transl_mul, mul_transl]
    simp only [kwD, add_sub_cancel_right]
    rw [phase_shift]
  · ext t s
    rw [Matrix.conjTranspose_apply, mul_transl]
    simp only [kwD, star_mul, star_pow, star_inv₀, star_sgn, Complex.star_def,
      Complex.conj_ofReal, add_sub_cancel_right]
    rw [phase_swap]
    exact mul_comm _ _
