-- Prove2me | solution 3 for OAI.PiExponent.FormalInterpolation.curve_bound_initial_ideal_powers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:20:31.59633+00:00
-- url     : https://prove2.me/submissions/3b031f59-1113-4d5f-af1b-75c810b52515
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_coordinate_powers
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_powers_to_exact_initial_ideal_positive_weights

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧
      0 < D ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
          ∃ g : MvPolynomial (Fin d) Complex,
            g ∈ I ^ s ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
            h = MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) g} := by
  obtain ⟨s, hs, B, hB, hmono⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_bounded_coordinate_powers
      I hfinite w hw rho hrho hcurve eps heps
  exact
    OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal_positive_weights
      I w ((rho : Real) + eps) hw ⟨s, hs, B, hB, hmono⟩