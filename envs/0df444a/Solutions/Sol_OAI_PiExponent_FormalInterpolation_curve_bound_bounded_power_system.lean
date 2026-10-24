-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:33:43.432389+00:00
-- url     : https://prove2.me/submissions/34358248-3f1d-4fa4-95be-66b9ea1de5c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_pointwise_sections_20261023_22
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_sections_finite_witness_20261023_22
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_origin_support_powers_20261023_22
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
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧ 0 < D ∧
      ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        (∀ i : Fin d, ∃ N : Nat, 0 < N ∧
          (MvPolynomial.X i) ^ N ∈ Ideal.span (Set.range (fun j : Fin m =>
            MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j)))) := by
  obtain ⟨s, hs, D, hD, hDpos, hpoint⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_22
      I hfinite w hw rho hrho hcurve eps heps
  obtain ⟨m, g, hpow, hweight, hzero⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_22
      I w s D hpoint
  refine ⟨s, hs, D, hD, hDpos, m, g, hpow, hweight, ?_⟩
  let q : Fin m → MvPolynomial (Fin d) Complex := fun j =>
    MvPolynomial.weightedHomogeneousComponent
      (fun k => (w k : ℚ)) (D : ℚ) (g j)
  have hzero' : ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) →
        ∀ i : Fin d, x i = 0 := by
    intro x hx
    exact hzero x (by
      intro j
      simpa [q] using hx j)
  have hpowers :=
    OAI.PiExponent.FormalInterpolation.origin_support_powers_20261023_22 q hzero'
  simpa [q] using hpowers