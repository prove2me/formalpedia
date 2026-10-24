-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_initial_ideal_powers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:52:57.135176+00:00
-- url     : https://prove2.me/submissions/ff1850cc-8b83-480a-9780-8c3bb1f798d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_sections
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_sections_exact_degree

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
  obtain ⟨s, hs, B, hB, hsections⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_bounded_sections
      I hfinite w hw rho hrho hcurve eps heps
  exact OAI.PiExponent.FormalInterpolation.bounded_sections_exact_degree
    I hfinite w hw rho hrho eps heps ⟨s, hs, B, hB, hsections⟩