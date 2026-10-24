-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_mem_span_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:08:23.990106+00:00
-- url     : https://prove2.me/submissions/9105bee6-c3c9-44b4-aca0-0af4e300e774

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_span_coefficients
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_X_pow_weightedHomogeneous

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (i : Fin d) (n : Nat) (hn : 0 < n)
    (hmem : (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n ∈ J) :
    ∃ c : Fin k → MvPolynomial (Fin d) Complex,
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n =
        ∑ j : Fin k, c j * g j ∧
      ∀ j, (c j).IsWeightedHomogeneous (fun l => (w l : Real))
        ((n : Real) * (w i : Real) - D) := by
  have hpow :
      ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n).IsWeightedHomogeneous
        (fun l => (w l : Real)) ((n : Real) * (w i : Real)) :=
    OAI.PiExponent.FormalInterpolation.X_pow_weightedHomogeneous
      (w := w) (i := i) (n := n)
  exact OAI.PiExponent.FormalInterpolation.weighted_span_coefficients
    (w := w) (D := D) (E := (n : Real) * (w i : Real)) (g := g)
    (J := J) (hspan := hspan)
    (f := (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n)
    (hhom := hhom) (hf := hpow) (hmem := hmem)