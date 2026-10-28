-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_rat_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:42:59.541886+00:00
-- url     : https://prove2.me/submissions/b3f3e6c3-81d9-4f47-93ec-122ea56fb6b7

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem solution {d : Nat} (w : Fin d -> Rat) (q : Rat)
    (p : MvPolynomial (Fin d) Complex) :
    MvPolynomial.weightedHomogeneousComponent
        (fun k => (w k : Real)) (q : Real) p =
      MvPolynomial.weightedHomogeneousComponent w q p := by
  classical
  ext e
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  have hweight :
      Finsupp.weight (fun k => (w k : Real)) e =
        (Finsupp.weight w e : Real) := by
    simp only [Finsupp.weight_eq_sum, nsmul_eq_mul]
    push_cast
    rfl
  by_cases h : Finsupp.weight w e = q
  case pos =>
    have hreal :
        Finsupp.weight (fun k => (w k : Real)) e = (q : Real) := by
      rw [hweight, h]
    simp [h, hreal]
  case neg =>
    have hreal :
        Not (Finsupp.weight (fun k => (w k : Real)) e = (q : Real)) := by
      intro h'
      apply h
      have hcast : (Finsupp.weight w e : Real) = (q : Real) := by
        simpa [hweight] using h'
      exact_mod_cast hcast
    simp [h, hreal]