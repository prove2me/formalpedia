-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.curve_bound_exact_rational_initial_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:08:16.220109+00:00
-- url     : https://prove2.me/submissions/204716c7-9f92-48e6-be0d-edeaed7b8120
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_component_ideal_finite_colength_20261024
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_ideal_finite_colength_coordinate_powers_20261024
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nat_between_rat_and_succ

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) ≤ (B : Real) ∧
        ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
          MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
            {g : MvPolynomial (Fin d) Complex //
              g ∈ I ^ s ∧
              ∀ a ∈ g.support,
                ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
            MvPolynomial.weightedHomogeneousComponent
              (fun j => (w j : ℚ)) q p.1)) := by
  obtain ⟨s, hs, q, hq, hmargin, hfiniteJ⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_bounded_component_ideal_finite_colength_20261024
      I hfinite w hw rho hrho hcurve eps heps
  let S : Set (MvPolynomial (Fin d) Complex) :=
    Set.range (fun (p : {g : MvPolynomial (Fin d) Complex //
      g ∈ I ^ s ∧ ∀ a ∈ g.support,
        ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : ℚ)) q p.1)
  have hhom : ∀ p ∈ S, ∃ g,
      p = MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : ℚ)) q g := by
    intro p hp
    rcases hp with ⟨u, rfl⟩
    exact ⟨u.1, rfl⟩
  have hcoords :=
    OAI.PiExponent.FormalInterpolation.homogeneous_ideal_finite_colength_coordinate_powers_20261024
      w hw q hq S hhom hfiniteJ
  obtain ⟨B, hqB, hBq⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_nat_between_rat_and_succ q hq
  refine ⟨s, hs, B, lt_trans hBq hmargin, q, hq, hqB, ?_⟩
  simpa [S] using hcoords