-- Prove2me | solution 1 for MasulloRH.truncated_euler_circle_second_derivative_gram
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:26:27.283362+00:00
-- url     : https://prove2.me/submissions/e86b90a4-3db5-44e5-b474-9113c867162f

import Mathlib
open AddCircle MeasureTheory
open scoped Real
theorem solution (T : ℝ) [Fact (0 < T)] (N : ℕ) :
    let P := fun x : ℝ => ∑ j ∈ Finset.range N, fourier (j:ℤ) (x : AddCircle T)
    (∀ x : ℝ, deriv (deriv P) x =
      -((2 * Real.pi / T : ℝ) : ℂ)^2 *
        ∑ j ∈ Finset.range N, (j:ℂ)^2 * fourier (j:ℤ) (x : AddCircle T)) ∧
    ‖∑ j ∈ Finset.range N, (j:ℂ)^2 • (@fourierLp T _ 2 _ (j:ℤ))‖^2 =
      (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30 := by
  classical
  intro P
  let C := fun j : ℕ => 2*(Real.pi:ℂ)*Complex.I*(j:ℂ)/(T:ℂ)
  let e := fun (j:ℕ) (x:ℝ) => fourier (j:ℤ) (x : AddCircle T)
  have de (j : ℕ) (x : ℝ) : HasDerivAt (e j) (C j * e j x) x := by
    simpa [e,C] using hasDerivAt_fourier T (j:ℤ) x
  constructor
  · have dP : deriv P = fun x => ∑ j ∈ Finset.range N, C j * e j x := by
      funext x
      exact (HasDerivAt.fun_sum (u := Finset.range N) (fun j _ => de j x)).deriv
    intro x
    rw [dP, (HasDerivAt.fun_sum (u := Finset.range N)
      (fun j _ => (de j x).const_mul (C j))).deriv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj : C j = ((2 * Real.pi / T : ℝ):ℂ) * Complex.I * (j:ℂ) := by
      dsimp [C]; push_cast; ring
    rw [hj]
    have alg (a z y : ℂ) : a * Complex.I * z * (a * Complex.I * z * y)
        = -a^2 * (z^2*y) := by
      calc
        _ = Complex.I^2 * (a^2 * (z^2*y)) := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    exact alg _ _ _
  · let v := fun j : ℕ => @fourierLp T _ 2 _ (j:ℤ)
    have hv : Orthonormal ℂ v := orthonormal_fourier.comp (fun j : ℕ => (j:ℤ)) Nat.cast_injective
    have heq := congrArg Complex.re (hv.inner_sum (fun j => (j:ℂ)^2)
      (fun j => (j:ℂ)^2) (Finset.range N))
    have hsum : ‖∑ j ∈ Finset.range N, (j:ℂ)^2 • v j‖^2 =
        ∑ j ∈ Finset.range N, (j:ℝ)^4 := by
      rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ]
      change Complex.re _ = _
      rw [heq]
      have key : (∑ j ∈ Finset.range N, (starRingEnd ℂ) ((j:ℂ)^2) * (j:ℂ)^2) =
          Complex.ofReal (∑ j ∈ Finset.range N, (j:ℝ)^4) := by
        push_cast
        apply Finset.sum_congr rfl
        intro j hj
        simp
        <;> ring
      rw [key]; rfl
    rw [show (‖∑ j ∈ Finset.range N, (j:ℂ)^2 • @fourierLp T _ 2 _ (j:ℤ)‖^2 : ℝ) = _ from hsum]
    clear hsum heq
    induction N with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
