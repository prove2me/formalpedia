-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_powers_of_finite_homogeneous_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:56:21.489187+00:00
-- url     : https://prove2.me/submissions/e7e834df-7e49-4f86-8e59-46dcd994360f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_coordinate_power_dependence
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_coordinate_power_sum_mem
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_from_nonzero_scalar_mem

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))] :
    ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N ∈ Ideal.span (Set.range p) := by
  intro i
  obtain ⟨K, c, hc, hsum⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_coordinate_power_dependence
      (I := Ideal.span (Set.range p)) i
  have hterms :=
    OAI.PiExponent.FormalInterpolation.homogeneous_coordinate_power_sum_mem
      w hw D hD m p hp i K c hsum
  obtain ⟨n, hn⟩ := hc
  exact OAI.PiExponent.FormalInterpolation.coordinate_power_from_nonzero_scalar_mem
    (I := Ideal.span (Set.range p)) i (n : ℕ) (c n) hn (hterms n)