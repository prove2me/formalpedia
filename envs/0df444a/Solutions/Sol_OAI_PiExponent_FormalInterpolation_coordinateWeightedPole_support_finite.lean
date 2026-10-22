-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateWeightedPole_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:42:57.714819+00:00
-- url     : https://prove2.me/submissions/2ce7f631-2c4f-445f-a058-81901666e98c

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_support_finite
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurvePole_support_subset_coordinate_poles
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (_hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) (k : Fin d) :
    Set.Finite {nu : PolynomialCurvePlace E | max (-(polynomialCurveOrder nu (x k) : Real)) 0 ≠ 0} ∧
      Set.Finite {nu : PolynomialCurvePlace E | polynomialCurvePole nu x w ≠ 0} := by
  classical
  have hcoord_of (j : Fin d) :
      Set.Finite {nu : PolynomialCurvePlace E |
        max (-(polynomialCurveOrder nu (x j) : Real)) 0 ≠ 0} := by
    refine (polynomialCurveOrder_support_finite htrdeg (x j)).subset ?_
    intro nu hnu
    have hpos : 0 < max (-(polynomialCurveOrder nu (x j) : Real)) 0 :=
      lt_of_le_of_ne (le_max_right _ _) hnu.symm
    have hneg : 0 < -(polynomialCurveOrder nu (x j) : Real) :=
      (lt_max_iff.mp hpos).resolve_right (lt_irrefl _)
    have : (polynomialCurveOrder nu (x j) : Real) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hcoord := hcoord_of k
  have hpoles : Set.Finite
      {nu : PolynomialCurvePlace E | polynomialCurvePole nu x w ≠ 0} := by
    have hsub := polynomialCurvePole_support_subset_coordinate_poles x w hw
    have hunion :
        Set.Finite (⋃ j : Fin d,
          {nu | max (-(polynomialCurveOrder nu (x j) : Real)) 0 ≠ 0}) :=
      Set.finite_iUnion fun j => hcoord_of j
    exact hunion.subset hsub
  exact ⟨hcoord, hpoles⟩
