-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_polynomial_coefficient_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T07:01:20.298009+00:00
-- url     : https://prove2.me/submissions/57d881bf-fcff-4446-9da6-b32ef765c817

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
open OAI.PiExponent

theorem solution
    {m : ℕ} (S : Finset (Fin (m + 1) → ℕ)) :
    ∀ y : ↑S → ℂ, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ a : ↑S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (Q : MvPowerSeries (Fin (m + 1)) ℂ) = y a := by
  classical
  intro y
  let Q : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ b : S, MvPolynomial.monomial (InterpolationMatrix.exponentVector b.val) (y b)
  refine ⟨Q, ?_⟩
  intro a
  simp [Q, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, InterpolationMatrix.exponentVector]