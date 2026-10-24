-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.positive_coeff_implies_coordinate_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:05:35.36152+00:00
-- url     : https://prove2.me/submissions/a3bbb1d9-34bd-462e-8e2e-ea73e73bc9b5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mem
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_polynomial_component

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (q : Polynomial ℂ) (n : Nat) (hn : 0 < n)
    (hqI : Polynomial.aeval (MvPolynomial.X i) q ∈ Ideal.span (Set.range p))
    (hcoeff : q.coeff n ≠ 0) :
    (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ Ideal.span (Set.range p) := by
  let I : Ideal (MvPolynomial (Fin d) ℂ) := Ideal.span (Set.range p)
  letI := MvPolynomial.weightedGradedAlgebra ℂ w
  have hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w) := by
    apply Ideal.homogeneous_span (MvPolynomial.weightedHomogeneousSubmodule ℂ w) (Set.range p)
    intro f hf
    rcases hf with ⟨j, rfl⟩
    exact ⟨(D : ℚ), hp j⟩
  have hwi : 0 < w i := by
    exact_mod_cast hw i
  have hcomponent :=
    OAI.PiExponent.FormalInterpolation.weighted_component_mem
      (w := w) (I := I) hI hqI (n * w i)
  rw [OAI.PiExponent.FormalInterpolation.coordinate_polynomial_component
    (w := w) (i := i) (q := q) (n := n) hwi] at hcomponent
  have hscaled : MvPolynomial.C ((q.coeff n)⁻¹) *
        (MvPolynomial.C (q.coeff n) * (MvPolynomial.X i) ^ n) ∈ I :=
    I.mul_mem_left _ hcomponent
  have hmul : MvPolynomial.C ((q.coeff n)⁻¹) * MvPolynomial.C (q.coeff n) =
      (1 : MvPolynomial (Fin d) ℂ) := by
    calc
      MvPolynomial.C ((q.coeff n)⁻¹) * MvPolynomial.C (q.coeff n) =
          MvPolynomial.C ((q.coeff n)⁻¹ * q.coeff n) := by
            exact (map_mul (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ) _ _).symm
      _ = MvPolynomial.C 1 := by rw [inv_mul_cancel₀ hcoeff]
      _ = 1 := map_one _
  rw [← mul_assoc, hmul, one_mul] at hscaled
  exact hscaled