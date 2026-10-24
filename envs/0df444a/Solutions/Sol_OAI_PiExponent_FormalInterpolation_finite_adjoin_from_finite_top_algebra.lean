-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_from_finite_top_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:07:40.975089+00:00
-- url     : https://prove2.me/submissions/2c13fec2-7a62-494d-b197-d0ca0b0e848a

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_power_relations_of_top_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_power_relations

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, (w i : Real) * (a i : Real) ≤ D)
    (htop : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j)))
    (hfinite : Module.Finite
      (Algebra.adjoin Complex
        (Set.range fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j)))
      (MvPolynomial (Fin d) Complex)) :
    Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin d) Complex) := by
  have hrel :=
    OAI.PiExponent.FormalInterpolation.homogeneous_power_relations_of_top_ideal
      w hw D hD f hweight htop
  exact
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_power_relations
      w hw D hD f hweight hrel