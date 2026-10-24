-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_bounded_weight_quotient_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:38:41.332011+00:00
-- url     : https://prove2.me/submissions/833b40a1-3720-434e-9a87-4c17097d4eee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_bounded_family_from_curve_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_representatives_of_finite_bounded_family

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ C : Real, 0 ≤ C ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C := by
  obtain ⟨s, hs, D, hD, m, g, hg, hdeg, hmod⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_bounded_family_from_curve_bound
      I hfinite w hw rho hrho hcurve eps heps
  exact
    OAI.PiExponent.FormalInterpolation.quotient_representatives_of_finite_bounded_family
      I w rho eps s hs D hD m g hg hdeg hmod
