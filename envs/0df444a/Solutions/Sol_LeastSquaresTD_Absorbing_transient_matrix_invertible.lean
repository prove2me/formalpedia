-- Prove2me | solution 1 for LeastSquaresTD.Absorbing.transient_matrix_invertible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:35:40.028458+00:00
-- url     : https://prove2.me/submissions/89a42d13-f4fe-4aac-a15b-4a771cebe229

import Mathlib
import Definitions.Def_LeastSquaresTD_Absorbing_Chain

set_option autoImplicit false

namespace AadeHelpers

lemma pow_nonneg' {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (hP : ∀ x y, 0 ≤ P x y) : ∀ n x y, 0 ≤ (P ^ n) x y := by
  intro n
  induction n with
  | zero =>
    intro x y
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hP z y))

lemma key {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (habs : ∀ x, ∃ (n : ℕ) (y : X), P y y = 1 ∧ 0 < (P ^ n) x y)
    (w : X → ℝ) (hw0 : ∀ x, P x x = 1 → w x = 0)
    (hw : ∀ x, P x x ≠ 1 → w x = γ * ∑ y, P x y * w y) : ∀ x, w x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x1, hx1⟩ := hcon
  obtain ⟨x0, -, hmax⟩ := Finset.exists_max_image Finset.univ w ⟨x1, Finset.mem_univ _⟩
  have hle : ∀ y, w y ≤ w x0 := fun y => hmax y (Finset.mem_univ _)
  have hm : 0 < w x0 := lt_of_lt_of_le hx1 (hle x1)
  have closure : ∀ z, w z = w x0 → ∀ y, 0 < P z y → w y = w x0 := by
    intro z hz y hy
    have hzN : P z z ≠ 1 := fun h => by rw [hw0 z h] at hz; linarith
    have hz' := hw z hzN
    have hsm : ∑ y, P z y * w y ≤ w x0 := by
      calc ∑ y, P z y * w y ≤ ∑ y, P z y * w x0 :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hle y) (hP z y))
        _ = w x0 := by rw [← Finset.sum_mul, hrow, one_mul]
    have hs_eq : ∑ y, P z y * w y = w x0 := by
      have h1 : 0 < γ * ∑ y, P z y * w y := by rw [← hz', hz]; exact hm
      have spos : 0 < ∑ y, P z y * w y := pos_of_mul_pos_right h1 hγ0
      nlinarith
    have hsum0 : ∑ y, P z y * (w x0 - w y) = 0 := by
      have : ∑ y, P z y * (w x0 - w y) = (∑ y, P z y) * w x0 - ∑ y, P z y * w y := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [this, hrow, hs_eq]; ring
    have hnn : ∀ y ∈ Finset.univ, 0 ≤ P z y * (w x0 - w y) :=
      fun y _ => mul_nonneg (hP z y) (by linarith [hle y])
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 y (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have reach : ∀ n y, 0 < (P ^ n) x0 y → w y = w x0 := by
    intro n
    induction n with
    | zero =>
      intro y hy
      by_cases h : x0 = y
      · subst h; rfl
      · rw [pow_zero, Matrix.one_apply, if_neg h] at hy; exact absurd hy (lt_irrefl 0)
    | succ n ih =>
      intro y hy
      rw [pow_succ, Matrix.mul_apply] at hy
      obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy.ne'
      have hz1 : (P ^ n) x0 z ≠ 0 := left_ne_zero_of_mul hz
      have hz2 : P z y ≠ 0 := right_ne_zero_of_mul hz
      exact closure z (ih z (lt_of_le_of_ne (pow_nonneg' P hP n x0 z) (Ne.symm hz1))) y
        (lt_of_le_of_ne (hP z y) (Ne.symm hz2))
  obtain ⟨n, y, hyy, hpos⟩ := habs x0
  have h1 := reach n y hpos
  rw [hw0 y hyy] at h1
  linarith

end AadeHelpers


-- Proof of Theorem 1, p. 44: the non-absorbing block of `I - γP` has full rank (0 ≤ γ ≤ 1).
open LeastSquaresTD.Absorbing in
theorem solution
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (γ : ℝ) (habs : C.IsAbsorbing)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsUnit ((1 - γ • C.P).submatrix
      (fun x : C.Nonabsorbing => x.val)
      (fun x : C.Nonabsorbing => x.val)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let w : X → ℝ := fun x => if h : C.P x x = 1 then 0 else v ⟨x, h⟩
  have hwv : ∀ j : C.Nonabsorbing, w j.val = v j := by
    intro j
    exact dif_neg j.property
  have hw0 : ∀ x, C.P x x = 1 → w x = 0 := by
    intro x hx
    simp only [w, dif_pos hx]
  have hsumeq : ∀ x, ∑ j : C.Nonabsorbing, C.P x j.val * v j = ∑ y, C.P x y * w y := by
    intro x
    have e1 : ∑ j : C.Nonabsorbing, C.P x j.val * v j
        = ∑ j : C.Nonabsorbing, C.P x j.val * w j.val :=
      Finset.sum_congr rfl (fun j _ => by rw [hwv j])
    rw [e1]
    have e2 : ∑ y ∈ Finset.univ.filter (fun y => C.P y y ≠ 1), C.P x y * w y
        = ∑ j : C.Nonabsorbing, C.P x j.val * w j.val :=
      Finset.sum_subtype (p := fun y => C.P y y ≠ 1) _ (by intro y; simp)
        (fun y => C.P x y * w y)
    rw [← e2, Finset.sum_filter_of_ne]
    intro y _ hne h
    exact hne (by rw [hw0 y (by simpa using h), mul_zero])
  have hw : ∀ x, C.P x x ≠ 1 → w x = γ * ∑ y, C.P x y * w y := by
    intro x hx
    have h := congrFun hv ⟨x, hx⟩
    change (∑ j : C.Nonabsorbing, (1 - γ • C.P) x j.val * v j) = 0 at h
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib] at h
    have h1 : ∑ j : C.Nonabsorbing, (1 : Matrix X X ℝ) x j.val * v j = v ⟨x, hx⟩ := by
      rw [Finset.sum_eq_single ⟨x, hx⟩]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply_ne, zero_mul]
        intro hxb
        exact hb (Subtype.ext hxb.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : ∑ j : C.Nonabsorbing, γ * C.P x j.val * v j
        = γ * ∑ j : C.Nonabsorbing, C.P x j.val * v j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, h2, hsumeq] at h
    rw [hwv ⟨x, hx⟩]
    linarith
  have hpos := AadeHelpers.key C.P C.nonneg C.row_sum γ hγ0 hγ1 habs w hw0 hw
  have hneg := AadeHelpers.key C.P C.nonneg C.row_sum γ hγ0 hγ1 habs (fun x => - w x)
    (fun x hx => by simp [hw0 x hx])
    (fun x hx => by
      rw [hw x hx]
      simp only [mul_neg, Finset.sum_neg_distrib])
  apply hv0
  funext j
  have := hpos j.val
  have := hneg j.val
  rw [← hwv j]
  simp only [Pi.zero_apply]
  linarith
