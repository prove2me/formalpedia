-- Prove2me | solution 1 for LeastSquaresTD.Absorbing.limit_matrix_invertible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:58:54.829039+00:00
-- url     : https://prove2.me/submissions/0712bf62-65e2-407f-9c7e-39a210dd2d8f

import Mathlib
import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

set_option autoImplicit false

namespace LSTD8601

open LeastSquaresTD.Absorbing

/-- Maximum-principle step: if `u` vanishes on absorbing states and satisfies
`u x = γ ∑ P x y u y` on non-absorbing states, then `u = 0`. -/
theorem u_eq_zero {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (γ : ℝ) (u : X → ℝ)
    (habs : C.IsAbsorbing) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (huabs : ∀ x, C.P x x = 1 → u x = 0)
    (hfix : ∀ x, C.P x x ≠ 1 → u x = γ * ∑ y, C.P x y * u y) :
    ∀ x, u x = 0 := by
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ (fun x => |u x|)
    Finset.univ_nonempty
  set M := |u x0| with hM
  have hle : ∀ x, |u x| ≤ M := fun x => hx0 x (Finset.mem_univ _)
  by_contra hne
  push Not at hne
  obtain ⟨x1, hx1⟩ := hne
  have hMpos : 0 < M := lt_of_lt_of_le (abs_pos.mpr hx1) (hle x1)
  -- closure: from a state attaining the max, every successor attains it
  have hclos : ∀ x, |u x| = M → ∀ y, 0 < C.P x y → |u y| = M := by
    intro x hx y hy
    have hxna : C.P x x ≠ 1 := by
      intro h; rw [huabs x h, abs_zero] at hx; linarith
    have hux := hfix x hxna
    have h1 : M ≤ γ * ∑ y, C.P x y * |u y| := by
      rw [← hx, hux, abs_mul, abs_of_nonneg hγ0]
      apply mul_le_mul_of_nonneg_left _ hγ0
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [abs_mul, abs_of_nonneg (C.nonneg x z)]
    have hs0 : 0 ≤ ∑ y, C.P x y * |u y| :=
      Finset.sum_nonneg (fun z _ => mul_nonneg (C.nonneg x z) (abs_nonneg _))
    have h2 : M ≤ ∑ y, C.P x y * |u y| := by
      have : γ * ∑ y, C.P x y * |u y| ≤ ∑ y, C.P x y * |u y| := by
        nlinarith
      linarith
    have h3 : ∑ y, C.P x y * (M - |u y|) = 0 := by
      have hsum : ∑ y, C.P x y * (M - |u y|) = M - ∑ y, C.P x y * |u y| := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, C.row_sum x, one_mul]
      have h4 : 0 ≤ ∑ y, C.P x y * (M - |u y|) :=
        Finset.sum_nonneg (fun z _ => mul_nonneg (C.nonneg x z) (by linarith [hle z]))
      linarith
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => mul_nonneg (C.nonneg x z) (by linarith [hle z]))).mp h3 y (Finset.mem_univ _)
    rcases mul_eq_zero.mp h5 with h | h
    · linarith
    · linarith
  have hx0M : |u x0| = M := rfl
  have hreach : ∀ n y, |u y| ≠ M → (C.P ^ n) x0 y = 0 := by
    intro n
    induction n with
    | zero =>
      intro y hy
      have : x0 ≠ y := by rintro rfl; exact hy hx0M
      simp [Matrix.one_apply_ne this]
    | succ n ih =>
      intro y hy
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      by_cases hz : |u z| = M
      · have : C.P z y = 0 := by
          rcases (C.nonneg z y).lt_or_eq with h | h
          · exact absurd (hclos z hz y h) hy
          · exact h.symm
        rw [this, mul_zero]
      · rw [ih z hz, zero_mul]
  obtain ⟨n, y, hyy, hpos⟩ := habs x0
  have hyM : |u y| = M := by
    by_contra h; rw [hreach n y h] at hpos; exact lt_irrefl _ hpos
  rw [huabs y hyy, abs_zero] at hyM
  linarith

end LSTD8601

open LeastSquaresTD.Absorbing Matrix in
theorem solution {m : ℕ}
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    (habs : C.IsAbsorbing) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hπ : ∀ x : C.Nonabsorbing, 0 < π x.val) :
    IsUnit (limitMatrix C φ γ π) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices H : ∀ w, limitMatrix C φ γ π *ᵥ w = 0 → w = 0 by
    intro a b hab
    have := H (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
    exact sub_eq_zero.mp this
  intro w hw
  set u : X → ℝ := fun x => φ x ⬝ᵥ w with hu_def
  have hu : Matrix.of φ *ᵥ w = u := rfl
  set z : X → ℝ := Matrix.diagonal π *ᵥ ((1 - γ • C.P) *ᵥ u) with hz_def
  have hw' : (Matrix.of φ)ᵀ *ᵥ z = 0 := by
    rw [← hw, hz_def, ← hu]
    simp only [limitMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : ∑ x, z x • φ x = 0 := by
    ext i
    have := congrFun hw' i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have hsumN : ∑ x : C.Nonabsorbing, z x.val • φ x.val = 0 := by
    rw [← hsum]
    rw [← Finset.sum_filter_of_ne (p := fun x => C.P x x ≠ 1)]
    · exact (Finset.sum_subtype (Finset.univ.filter (fun x => C.P x x ≠ 1))
        (by simp) (fun x => z x • φ x)).symm
    · intro x _ hx hxx
      apply hx
      rw [hφabs x hxx, smul_zero]
  have hzN := Fintype.linearIndependent_iff.mp hli (fun x => z x.val) hsumN
  have hQ : ∀ x, ((1 - γ • C.P) *ᵥ u) x = u x - γ * ∑ y, C.P x y * u y := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
  have hfix : ∀ x, C.P x x ≠ 1 → u x = γ * ∑ y, C.P x y * u y := by
    intro x hx
    have h0 : z x = 0 := hzN ⟨x, hx⟩
    rw [hz_def, Matrix.mulVec_diagonal, hQ] at h0
    have hp : π x ≠ 0 := (hπ ⟨x, hx⟩).ne'
    have := (mul_eq_zero.mp h0).resolve_left hp
    linarith
  have huabs : ∀ x, C.P x x = 1 → u x = 0 := by
    intro x hx
    simp [hu_def, hφabs x hx]
  have hu0 := LSTD8601.u_eq_zero C γ u habs hγ0 hγ1 huabs hfix
  let e : C.Nonabsorbing ≃ Fin m := Fintype.equivFinOfCardEq hm.symm
  let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i => φ (e.symm i).val
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  apply Matrix.mulVec_injective_iff_isUnit.mpr hA
  rw [Matrix.mulVec_zero]
  funext i
  exact hu0 (e.symm i).val

