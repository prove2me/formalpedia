-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_power_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:50:11.334828+00:00
-- url     : https://prove2.me/submissions/5445db7d-c9bf-4b27-9781-7268e2b2a085

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_coordinate_power_witness
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_from_weighted_coordinate_reductions

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (hpowers : ∀ i, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n ∈ J) :
    Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  obtain ⟨n, hn, c, heq, hc⟩ :=
    OAI.PiExponent.FormalInterpolation.homogeneous_coordinate_power_witness
      w hw D hD g hhom J hspan hpowers
  exact OAI.PiExponent.FormalInterpolation.finite_from_weighted_coordinate_reductions
    w hw D hD g hhom n hn c heq hc