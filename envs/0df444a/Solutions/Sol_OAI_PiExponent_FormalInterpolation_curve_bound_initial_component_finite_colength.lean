-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_initial_component_finite_colength
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T08:58:29.929971+00:00
-- url     : https://prove2.me/submissions/0983b0bc-14f7-4b08-a7a0-e173ffe5507f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_initial_component_coordinate_powers_for_finite_colength_retry
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_finite_quotient
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸
        Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1))) := by
  obtain ⟨s, hs, q, hq, hslack, hcoordinate_powers⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_bounded_initial_component_coordinate_powers_for_finite_colength_retry
      I hfinite w hw rho hrho hcurve eps heps
  let J : Nat → Rat → Ideal (MvPolynomial (Fin d) Complex) := fun s q =>
    Ideal.span (Set.range (fun (p :
      {g : MvPolynomial (Fin d) Complex //
        g ∈ I ^ s ∧
        ∀ a ∈ g.support,
          ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : ℚ)) q p.1))
  have hpowers : ∀ i : Fin d, ∃ N : Nat, MvPolynomial.X i ^ N ∈ J s q :=
    hcoordinate_powers
  have hquotient : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ J s q) :=
    OAI.PiExponent.FormalInterpolation.coordinate_powers_finite_quotient
      (J s q) hpowers
  exact ⟨s, hs, q, hq, hslack, by simpa [J] using hquotient⟩