-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_span_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:13:01.173119+00:00
-- url     : https://prove2.me/submissions/55e3b204-ca63-4b85-bdbb-341cf6b8dce1

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_span_representation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_explicit_representation_extract

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat)
    (D E : Real) (g : Fin k → MvPolynomial (Fin d) Complex)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (f : MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (hf : f.IsWeightedHomogeneous (fun i => (w i : Real)) E)
    (hmem : f ∈ J) :
    ∃ c : Fin k → MvPolynomial (Fin d) Complex,
      f = ∑ j : Fin k, c j * g j ∧
      ∀ j, (c j).IsWeightedHomogeneous (fun i => (w i : Real)) (E - D) := by
  obtain ⟨a, ha⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_span_representation
      g J hspan f hmem
  exact
    OAI.PiExponent.FormalInterpolation.weighted_explicit_representation_extract
      w D E g f a hhom hf ha