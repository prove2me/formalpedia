-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_power_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:40:29.854586+00:00
-- url     : https://prove2.me/submissions/2cf9ff9b-5270-436a-a2c6-57cd54739093

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_coordinate_powers
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_finite_homogeneous_quotient
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (f : Fin k → MvPolynomial (Fin d) Complex)
    (htop : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j))) :
    Module.Finite
      (Algebra.adjoin Complex
        (Set.range fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j)))
      (MvPolynomial (Fin d) Complex) := by
  let g : Fin k → MvPolynomial (Fin d) Complex := fun j =>
    MvPolynomial.weightedHomogeneousComponent (fun i : Fin d => (w i : Real)) D (f j)
  let J : Ideal (MvPolynomial (Fin d) Complex) := Ideal.span (Set.range g)
  have hfinite : Module.Finite Complex ((MvPolynomial (Fin d) Complex) ⧸ J) :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers J htop
  have hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i : Fin d => (w i : Real)) D := by
    intro j
    change (MvPolynomial.weightedHomogeneousComponent
      (fun i : Fin d => (w i : Real)) D (f j)).IsWeightedHomogeneous
      (fun i : Fin d => (w i : Real)) D
    exact @MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      Complex Real inferInstance (Fin d) inferInstance
      (fun i : Fin d => (w i : Real)) D (f j)
  have hspan : Ideal.span (Set.range g) = J := rfl
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_of_finite_homogeneous_quotient
    w hw D hD g hhom J hspan hfinite