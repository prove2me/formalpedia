-- Prove2me | solution 1 for NullConeGravity.finite_spectrum_gaussian_trace
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:46:18.647842+00:00
-- url     : https://prove2.me/submissions/60841e21-299a-4127-8974-b716d1a71886

import Theorems.Thm_NullConeGravity_gaussian_area_window_normalization
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Set MeasureTheory
open NullConeGravity

/-- Integrating a finite Gaussian spectral sum returns its total weight. -/
private theorem integrate_spectral_weights {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (w : ι → ℂ) :
    (∫ t in Ioi (0 : ℝ),
      (∑ i, w i * (Real.exp (-((s i - t) ^ 2) / (4 * t)) : ℂ)) /
        (Real.sqrt (4 * Real.pi * t) : ℂ)) = ∑ i, w i := by
  let K (i : ι) (t : ℝ) : ℝ :=
    Real.exp (-((s i - t) ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t)
  have hnorm (i : ι) : (∫ t in Ioi (0 : ℝ), K i t) = 1 :=
    gaussian_area_window_normalization (s i) (hs i)
  have hcomplex (i : ι) : (∫ t in Ioi (0 : ℝ), (K i t : ℂ)) = 1 := by
    rw [integral_complex_ofReal, hnorm, Complex.ofReal_one]
  have hint (i : ι) : Integrable (fun t => (K i t : ℂ)) (volume.restrict (Ioi 0)) := by
    by_contra h
    have hz := integral_undef h
    rw [hcomplex i] at hz
    exact one_ne_zero hz
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∑ i, w i * (K i t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      simp only [K, Complex.ofReal_div, mul_div_assoc]
    _ = ∑ i, w i := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hint i).const_mul (w i))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, hcomplex, mul_one]

theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (C : Matrix κ ι ℂ) :
    let Cb (t : ℝ) := C * Matrix.diagonal (fun i =>
      (Real.sqrt (Real.exp (-((s i - t) ^ 2) / (4 * t))) : ℂ))
    Matrix.trace (C.conjTranspose * C) =
      ∫ t in Ioi (0 : ℝ), Matrix.trace ((Cb t).conjTranspose * Cb t) /
        (Real.sqrt (4 * Real.pi * t) : ℂ) := by
  let f (i : ι) (t : ℝ) := Real.exp (-((s i - t) ^ 2) / (4 * t))
  let d (t : ℝ) (i : ι) : ℂ := Real.sqrt (f i t)
  let D (t : ℝ) : Matrix ι ι ℂ := Matrix.diagonal (d t)
  let A := C.conjTranspose * C
  have hD (t : ℝ) : (D t).conjTranspose = D t := by
    unfold D
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [d]
  have hsquare (t : ℝ) (i : ι) : d t i * d t i = (f i t : ℂ) := by
    unfold d
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.exp_pos _).le]
  have htrace (t : ℝ) : Matrix.trace ((C * D t).conjTranspose * (C * D t)) =
      ∑ i, A i i * (f i t : ℂ) := by
    rw [Matrix.conjTranspose_mul, hD]
    calc
      _ = Matrix.trace ((D t * A) * D t) := by simp only [A, Matrix.mul_assoc]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply, D, Matrix.mul_diagonal, Matrix.diagonal_mul]
        apply Finset.sum_congr rfl
        intro i _
        change d t i * A i i * d t i = A i i * (f i t : ℂ)
        calc
          _ = A i i * (d t i * d t i) := by ring
          _ = _ := by rw [hsquare]
  change Matrix.trace A = ∫ t in Ioi (0 : ℝ),
    Matrix.trace ((C * D t).conjTranspose * (C * D t)) / (Real.sqrt (4 * Real.pi * t) : ℂ)
  simp_rw [htrace]
  exact (integrate_spectral_weights s hs (fun i => A i i)).symm
