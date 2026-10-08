-- Prove2me | solution 1 for Matrix.PosDef.map_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T08:47:28.41405+00:00
-- url     : https://prove2.me/submissions/f5b16f66-634c-411e-ae6e-8241591777df

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open scoped ComplexOrder
open Matrix Complex Filter Topology

/-!
# Reusable children of leaf C1

* `Matrix.hasDerivAt_nonsing_inv_apply`: entrywise derivative of the inverse of a differentiable
  path of complex matrices at a point where it is invertible, `(M⁻¹)' = -M⁻¹ M' M⁻¹`.
* `Matrix.PosDef.map_ofReal`: a real positive definite matrix is positive definite over `ℂ`.
-/



lemma Matrix.differentiableAt_det_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℝ → Matrix n n ℂ} {t : ℝ} (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  simp only [Matrix.det_apply']
  fun_prop

theorem Matrix.hasDerivAt_nonsing_inv_apply' {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℝ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℝ}
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t) (ht : (M t).det ≠ 0) (i j : n) :
    HasDerivAt (fun s => (M s)⁻¹ i j) ((-((M t)⁻¹ * M' * (M t)⁻¹)) i j) t := by
  have hMd : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t := fun a b => (hM a b).differentiableAt
  -- differentiability of the inverse entries (Cramer's rule)
  have hinv : ∀ a b, DifferentiableAt ℝ (fun s => (M s)⁻¹ a b) t := by
    intro a b
    simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
      Matrix.adjugate_apply]
    refine ((Matrix.differentiableAt_det_of_entries hMd).inv ht).mul
      (Matrix.differentiableAt_det_of_entries fun r c => ?_)
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableAt_const _
    · exact hMd r c
  set D : Matrix n n ℂ := Matrix.of fun a b => deriv (fun s => (M s)⁻¹ a b) t with hD
  have hDd : ∀ a b, HasDerivAt (fun s => (M s)⁻¹ a b) (D a b) t := fun a b => (hinv a b).hasDerivAt
  -- `M s * (M s)⁻¹ = 1` near `t`
  have hev : ∀ᶠ s in 𝓝 t, (M s).det ≠ 0 :=
    (Matrix.differentiableAt_det_of_entries hMd).continuousAt.eventually_ne ht
  have hprod : ∀ a b, HasDerivAt (fun s => (M s * (M s)⁻¹) a b) ((M' * (M t)⁻¹ + M t * D) a b) t := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun k _ => (hM a k).mul (hDd k b)
  have hone : ∀ a b, HasDerivAt (fun s => (M s * (M s)⁻¹) a b) 0 t := by
    intro a b
    refine (hasDerivAt_const t ((1 : Matrix n n ℂ) a b)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs)]
  have heq : M' * (M t)⁻¹ + M t * D = 0 := by
    ext a b; exact (hprod a b).unique (hone a b)
  have hu : IsUnit (M t).det := isUnit_iff_ne_zero.mpr ht
  have key : D = -((M t)⁻¹ * M' * (M t)⁻¹) := by
    have h2 : M t * D = -(M' * (M t)⁻¹) := eq_neg_of_add_eq_zero_right heq
    calc D = (M t)⁻¹ * (M t * D) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -((M t)⁻¹ * M' * (M t)⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← key]
  exact hDd i j

theorem Matrix.PosDef.map_ofReal' {n : Type*} [Fintype n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    (M.map (fun x : ℝ => (x : ℂ))).PosDef := by
  have hs : Mᵀ = M := by
    have := hM.1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ i j, M j i = M i j := fun i j => by rw [← Matrix.transpose_apply M i j, hs]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, hsym]
  set u : n → ℝ := fun i => (x i).re
  set v : n → ℝ := fun i => (x i).im
  have hterm : ∀ i j, star (x i) * ((M i j : ℂ) * x j) =
      ((M i j * (u i * u j + v i * v j) : ℝ) : ℂ) +
        ((M i j * (u i * v j - v i * u j) : ℝ) : ℂ) * I := by
    intro i j; apply Complex.ext <;> simp [u, v] <;> ring
  have him : ∑ i, ∑ j, M i j * (u i * v j - v i * u j) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]; ring
  have hre : ∑ i, ∑ j, M i j * (u i * u j + v i * v j) = u ⬝ᵥ (M *ᵥ u) + v ⬝ᵥ (M *ᵥ v) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have key : star x ⬝ᵥ ((M.map (fun x : ℝ => (x : ℂ))) *ᵥ x) =
      ((u ⬝ᵥ (M *ᵥ u) + v ⬝ᵥ (M *ᵥ v) : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, hterm,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, him, hre]
    simp
  rw [key, Complex.zero_lt_real]
  have hu : 0 ≤ u ⬝ᵥ (M *ᵥ u) := by
    by_cases h : u = 0
    · simp [h]
    · simpa using (hM.dotProduct_mulVec_pos h).le
  have hv : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    by_cases h : v = 0
    · simp [h]
    · simpa using (hM.dotProduct_mulVec_pos h).le
  by_cases h : u = 0
  · have hv0 : v ≠ 0 := by
      intro hv0; apply hx; funext i; apply Complex.ext
      · simpa [u] using congrFun h i
      · simpa [v] using congrFun hv0 i
    have := hM.dotProduct_mulVec_pos hv0
    simp only [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    linarith

open Matrix.PosDef

theorem solution {n : Type*} [Fintype n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    (M.map (fun x : ℝ => (x : ℂ))).PosDef :=
  Matrix.PosDef.map_ofReal' hM
