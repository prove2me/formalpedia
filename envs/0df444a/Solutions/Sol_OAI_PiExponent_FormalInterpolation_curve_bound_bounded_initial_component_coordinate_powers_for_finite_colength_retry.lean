-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_bounded_initial_component_coordinate_powers_for_finite_colength_retry
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:13:18.616836+00:00
-- url     : https://prove2.me/submissions/3230afa7-0176-430b-b19e-a9cd2def20ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_finite_initial_power_certificate

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
      ∀ i : Fin d, ∃ N : Nat,
        MvPolynomial.X i ^ N ∈
          Ideal.span (Set.range (fun (p :
            {g : MvPolynomial (Fin d) Complex //
              g ∈ I ^ s ∧
              ∀ a ∈ g.support,
                ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
            MvPolynomial.weightedHomogeneousComponent
              (fun j => (w j : ℚ)) q p.1)) := by
  obtain ⟨s, hs, q, hq, hslack, n, f, hfI, hfsupport, hgen⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_curve_bound_finite_initial_power_certificate
      I hfinite w hw rho hrho hcurve eps heps
  refine ⟨s, hs, q, hq, hslack, ?_⟩
  intro i
  obtain ⟨N, hN⟩ := hgen i
  refine ⟨N, ?_⟩
  refine (Ideal.span_mono ?_) hN
  intro z hz
  rcases hz with ⟨j, rfl⟩
  refine ⟨⟨f j, hfI j, ?_⟩, rfl⟩
  intro a ha
  exact hfsupport j a ha