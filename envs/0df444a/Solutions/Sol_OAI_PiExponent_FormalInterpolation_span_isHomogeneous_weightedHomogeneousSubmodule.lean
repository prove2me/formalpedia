-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.span_isHomogeneous_weightedHomogeneousSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:28:20.90352+00:00
-- url     : https://prove2.me/submissions/8678b707-1f8d-416a-a37a-540251c489df

import Mathlib

theorem solution
    {d m : Nat} (w : Fin d → ℚ) (D : ℚ)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) D)
    [GradedRing (MvPolynomial.weightedHomogeneousSubmodule ℂ w)] :
    (Ideal.span (Set.range p)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ w) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨j, rfl⟩
  exact ⟨D, (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ w D (p j)).2 (hp j)⟩
