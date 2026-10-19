-- Prove2me | solution 1 for KramersWannier.kw_fusion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:15:45.799379+00:00
-- url     : https://prove2.me/submissions/2ca345ba-f428-48b8-9e69-b8b85f2f0caf

import Definitions.Def_KramersWannier_defs

open Matrix
open Fin.NatCast
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

private lemma phase_swap {L : ℕ} [NeZero L] (t s : Config L) :
    phase t s = phase (fun k => s (k + 1)) t := by
  have h := Equiv.sum_comp (Equiv.addRight (1 : Fin L))
    (fun k => s k * t k)
  simp only [Equiv.coe_addRight] at h
  simp only [phase, mul_add, Finset.sum_add_distrib]
  rw [h]
  simp only [mul_comm]
  exact add_comm _ _

private lemma cyclic_constant {L : ℕ} [NeZero L] (a : Config L)
    (h : ∀ j, a j + a (j - 1) = 0) : ∀ j, a j = a 0 := by
  have hs (j : Fin L) : a (j + 1) = a j := by
    have hj := h (j + 1)
    simp only [add_sub_cancel_right] at hj
    have he := congrArg (fun z => z + a j) hj
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using he
  intro j
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have he : j.succ = j.castSucc + 1 := by
      apply Fin.ext
      simp
    rw [he, hs, ih]

private lemma binary (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl

private lemma sum_character {L : ℕ} [NeZero L] (a : Config L) :
    (∑ r : Config L, sgn (phase a r)) =
      if a = 0 ∨ a = 1 then (2 : ℂ) ^ L else 0 := by
  classical
  by_cases h : ∀ j, a j + a (j - 1) = 0
  · have hc := cyclic_constant a h
    have ha : a = 0 ∨ a = 1 := by
      have hb := binary (a 0)
      rcases hb with hb | hb
      · left; ext j; exact (hc j).trans hb
      · right; ext j; exact (hc j).trans hb
    rw [if_pos ha]
    have hp (r : Config L) : phase a r = 0 := by
      rcases ha with rfl | rfl
      · simp [phase]
      · have hr := Equiv.sum_comp (Equiv.addRight (1 : Fin L)) r
        simp only [phase, Pi.one_apply, one_mul, Finset.sum_add_distrib,
          Equiv.coe_addRight] at *
        rw [hr, CharTwo.add_self_eq_zero]
    simp [hp, sgn, ZMod.card]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    have hval : a j + a (j - 1) = 1 := by
      have hb := binary (a j + a (j - 1))
      exact hb.resolve_left hj
    have hn : ¬ (a = 0 ∨ a = 1) := by
      rintro (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero] at hj
    rw [if_neg hn]
    have he := Equiv.sum_comp (Equiv.addRight (Pi.single j 1 : Config L))
      (fun r => sgn (phase a r))
    simp only [Equiv.coe_addRight, phase_add_right, phase_single_right, hval, sgn_add] at he
    have hone : sgn (1 : ZMod 2) = -1 := by norm_num [sgn]
    simp only [hone, mul_neg_one, Finset.sum_neg_distrib] at he
    linear_combination -(1 / 2 : ℂ) * he

private lemma shift_eq {L : ℕ} [NeZero L] (t s : Config L) :
    t = (fun k => s (k - 1)) ↔ s = (fun k => t (k + 1)) := by
  constructor <;> intro h <;> subst_vars <;> ext k <;> simp

private lemma transl_mul {L : ℕ} [NeZero L] (A : Op L) (t s : Config L) :
    (transl L * A) t s = A (fun k => t (k + 1)) s := by
  simp only [Matrix.mul_apply, transl, shift_eq t, ite_mul, one_mul, zero_mul]
  simp

private lemma flip_eq {L : ℕ} (t s a : Config L) :
    t = s + a ↔ s = t + a := by
  constructor <;> intro h <;> subst_vars <;> ext k <;>
    simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private lemma eta_mul {L : ℕ} (A : Op L) (t s : Config L) :
    (eta L * A) t s = A (t + 1) s := by
  simp only [Matrix.mul_apply, eta, flip_eq t, ite_mul, one_mul, zero_mul]
  simp

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

private lemma normalization (L : ℕ) :
    (((Real.sqrt 2 : ℂ)⁻¹) ^ L * ((Real.sqrt 2 : ℂ)⁻¹) ^ L) * (2 : ℂ) ^ L = 1 := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hc : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 := by
    rw [← sq, inv_pow, hs]
    norm_num
  rw [← mul_pow, ← mul_pow, hc, one_pow]

private lemma add_eq_zero {L : ℕ} (t s : Config L) : t + s = 0 ↔ t = s := by
  have hss : s + s = 0 := by ext k; exact CharTwo.add_self_eq_zero _
  constructor
  · intro h
    have he := congrArg (fun z => z + s) h
    simpa only [add_assoc, hss, add_zero, zero_add] using he
  · rintro rfl
    exact hss

private lemma add_eq_one {L : ℕ} (t s : Config L) : t + s = 1 ↔ t = s + 1 := by
  have hss : s + s = 0 := by ext k; exact CharTwo.add_self_eq_zero _
  constructor
  · intro h
    have he := congrArg (fun z => z + s) h
    simpa only [add_assoc, hss, add_zero, add_comm 1 s] using he
  · rintro rfl
    rw [add_right_comm, hss, zero_add]

private lemma product_entry {L : ℕ} [NeZero L] (t s : Config L) :
    (kwD L * kwD L) t s =
      (if t = (fun k => s (k + 1)) then 1 else 0) +
      (if t = (fun k => s (k + 1)) + 1 then 1 else 0) := by
  classical
  let a : Config L := t + (fun k => s (k + 1))
  have he (r : Config L) :
      kwD L t r * kwD L r s =
        (((Real.sqrt 2 : ℂ)⁻¹) ^ L * ((Real.sqrt 2 : ℂ)⁻¹) ^ L) * sgn (phase a r) := by
    change (_ * sgn (phase t r)) * (_ * sgn (phase r s)) = _
    rw [show phase a r = phase t r + phase (fun k => s (k + 1)) r from
      phase_add_left _ _ _, ← phase_swap r s, sgn_add]
    ring
  simp only [Matrix.mul_apply, he, ← Finset.mul_sum]
  rw [sum_character]
  have hn := normalization L
  have h01 : (0 : Config L) ≠ 1 := by
    intro h
    have he := congrFun h (0 : Fin L)
    norm_num at he
  have h0 : a = 0 ↔ t = (fun k => s (k + 1)) := add_eq_zero _ _
  have h1 : a = 1 ↔ t = (fun k => s (k + 1)) + 1 := add_eq_one _ _
  simp only [← h0, ← h1]
  by_cases ha0 : a = 0
  · simpa [ha0, h01] using hn
  · by_cases ha1 : a = 1
    · simpa [ha1, Ne.symm h01] using hn
    · simp [ha0, ha1]

end KramersWannier

open KramersWannier

theorem solution (L : ℕ) [NeZero L] :
    kwD L * kwD L = (1 + eta L) * (transl L)⁻¹ := by
  ext t s
  rw [product_entry, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, eta_mul, transl_inv]
  change _ = (if t = (fun k => s (k + 1)) then (1 : ℂ) else 0) +
    if t + 1 = (fun k => s (k + 1)) then 1 else 0
  simp only [flip_eq t (fun k => s (k + 1)) 1, eq_comm]
