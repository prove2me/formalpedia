-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_asymptotic_initial_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:25:25.194905+00:00
-- url     : https://prove2.me/submissions/3cc33c3e-7d08-47bd-b9ca-f84735ffd7ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_finite_weighted_power_certificate

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (R : Real) (hR : (rho : Real) < R) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun p :
              {g : MvPolynomial (Fin d) Complex //
                g ∈ I ^ s ∧
                ∀ a ∈ g.support,
                  ∑ j, (w j : Real) * (a j : Real) ≤ D} =>
              MvPolynomial.weightedHomogeneousComponent
                (fun j => (w j : Real)) D p.1)) := by
  obtain ⟨s, hs, D, hD, hDR, n, f, hf, hwt, hgen⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_finite_weighted_power_certificate
      I hfinite w hw rho hrho hcurve R hR
  refine ⟨s, hs, D, hD, hDR, fun i => ?_⟩
  obtain ⟨e, he, hmem⟩ := hgen i
  refine ⟨e, he, ?_⟩
  have hsub :
      Set.range (fun j : Fin n =>
        MvPolynomial.weightedHomogeneousComponent (fun k => (w k : Real)) D (f j)) ⊆
      Set.range (fun p :
        {g : MvPolynomial (Fin d) Complex //
          g ∈ I ^ s ∧
          ∀ a ∈ g.support, ∑ j, (w j : Real) * (a j : Real) ≤ D} =>
        MvPolynomial.weightedHomogeneousComponent (fun k => (w k : Real)) D p.1) := by
    rintro y ⟨j, rfl⟩
    exact ⟨⟨f j, hf j, hwt j⟩, rfl⟩
  exact (Ideal.span_mono hsub) hmem