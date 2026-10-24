-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_common_weight_initial_forms
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:01:14.552519+00:00
-- url     : https://prove2.me/submissions/d03173c3-73ab-4242-9857-0fb23790a339

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_coordinate_power_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_from_finite_top_algebra

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, (w i : Real) * (a i : Real) ≤ D)
    (htop : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j)))) :
    Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin d) Complex) := by
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_from_finite_top_algebra
    w hw D hD f hweight htop
    (OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_power_ideal
      w hw D hD f htop)