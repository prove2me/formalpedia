-- Prove2me | solution 1 for KramersWannier.z2_translation_algebra
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:07:51.132356+00:00
-- url     : https://prove2.me/submissions/4d4b04f0-08d3-491d-ba4f-2356b38febd3

import Definitions.Def_KramersWannier_defs

open Matrix
open Fin.NatCast
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

private lemma flip_eq {L : ℕ} (t s a : Config L) :
    t = s + a ↔ s = t + a := by
  constructor <;> intro h <;> subst_vars <;> ext k <;>
    simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private lemma eta_mul {L : ℕ} (A : Op L) (t s : Config L) :
    (eta L * A) t s = A (t + 1) s := by
  simp only [Matrix.mul_apply, eta, flip_eq t, ite_mul, one_mul, zero_mul]
  simp

private lemma mul_eta {L : ℕ} (A : Op L) (t s : Config L) :
    (A * eta L) t s = A t (s + 1) := by
  simp [Matrix.mul_apply, eta]

private lemma transl_pow {L : ℕ} [NeZero L] (n : ℕ) (t s : Config L) :
    (transl L ^ n) t s = if t = (fun k => s (k - (Nat.cast n : Fin L))) then 1 else 0 := by
  induction n generalizing s with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, mul_transl, ih]
    simp only [Nat.cast_add, Nat.cast_one, sub_sub]

private lemma transl_inv {L : ℕ} [NeZero L] :
    (transl L)⁻¹ = Matrix.of (fun t s => if t = (fun k => s (k + 1)) then 1 else 0) := by
  apply Matrix.inv_eq_right_inv
  ext t s
  rw [transl_mul]
  change (if (fun k => t (k + 1)) = (fun k => s (k + 1)) then (1 : ℂ) else 0) = _
  have h : (fun k => t (k + 1)) = (fun k => s (k + 1)) ↔ t = s := by
    constructor
    · intro h
      ext k
      simpa using congrFun h (k - 1)
    · rintro rfl; rfl
  simp [h, Matrix.one_apply]

private lemma single_shift {L : ℕ} [NeZero L] (j : Fin L) :
    (fun k => ((Pi.single j 1 : Config L)) (k - 1)) = (Pi.single (j + 1) 1 : Config L) := by
  ext k
  simp only [Pi.single_apply]
  simp only [sub_eq_iff_eq_add]

private lemma sgn_one_add (a : ZMod 2) : sgn (a + 1) = -sgn a := by
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases ha with rfl | rfl <;> simp [sgn, h]

end KramersWannier

open KramersWannier

theorem solution (L : ℕ) [NeZero L] :
    eta L * eta L = 1 ∧ transl L * eta L = eta L * transl L ∧ transl L ^ L = 1 ∧
    (∀ j : Fin L, transl L * pauliX L j * (transl L)⁻¹ = pauliX L (j + 1)) ∧
    (∀ j : Fin L, transl L * pauliZ L j * (transl L)⁻¹ = pauliZ L (j + 1)) ∧
    (∀ j : Fin L, eta L * pauliX L j = pauliX L j * eta L) ∧
    (∀ j : Fin L, eta L * pauliZ L j = -(pauliZ L j * eta L)) := by
  have hTi : transl L * (transl L)⁻¹ = 1 := by
    rw [transl_inv]
    ext t s
    rw [transl_mul]
    change (if (fun k => t (k + 1)) = (fun k => s (k + 1)) then (1 : ℂ) else 0) = _
    have h : (fun k => t (k + 1)) = (fun k => s (k + 1)) ↔ t = s := by
      constructor
      · intro h; ext k; simpa using congrFun h (k - 1)
      · rintro rfl; rfl
    simp [h, Matrix.one_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext t s
    rw [mul_eta]
    simp [eta, add_assoc, CharTwo.add_self_eq_zero, Matrix.one_apply]
  · ext t s
    rw [mul_eta, eta_mul]
    change (if t = (fun k => s (k - 1)) + 1 then (1 : ℂ) else 0) =
      if t + 1 = (fun k => s (k - 1)) then 1 else 0
    simp only [flip_eq t (fun k => s (k - 1)) 1, eq_comm]
  · ext t s
    simp [transl_pow, Matrix.one_apply]
  · intro j
    have h : transl L * pauliX L j = pauliX L (j + 1) * transl L := by
      ext t s
      rw [transl_mul, mul_transl]
      simp only [pauliX]
      have he : (fun k => t (k + 1)) = s + Pi.single j 1 ↔
          t = (fun k => s (k - 1)) + Pi.single (j + 1) 1 := by
        rw [← single_shift]
        constructor
        · intro h; ext k; simpa using congrFun h (k - 1)
        · intro h; ext k; simpa using congrFun h (k + 1)
      simp only [he]
    rw [h, Matrix.mul_assoc, hTi, Matrix.mul_one]
  · intro j
    have h : transl L * pauliZ L j = pauliZ L (j + 1) * transl L := by
      ext t s
      simp only [pauliZ, Matrix.mul_diagonal, Matrix.diagonal_mul, transl]
      split_ifs with h
      · subst t; simp
      · simp
    rw [h, Matrix.mul_assoc, hTi, Matrix.mul_one]
  · intro j
    ext t s
    rw [eta_mul]
    simp only [Matrix.mul_apply, pauliX, flip_eq t, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change (if t + 1 = s + Pi.single j 1 then (1 : ℂ) else 0) =
      if t + Pi.single j 1 = s + 1 then 1 else 0
    simp only [flip_eq (t + 1) s (Pi.single j 1),
      flip_eq (t + Pi.single j 1) s 1, add_right_comm t 1 (Pi.single j 1)]
  · intro j
    ext t s
    simp only [pauliZ, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, eta]
    split_ifs with h
    · subst t; simp [sgn_one_add]
    · simp
