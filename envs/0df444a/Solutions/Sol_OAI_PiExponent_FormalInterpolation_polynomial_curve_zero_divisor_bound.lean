-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomial_curve_zero_divisor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:44:45.785879+00:00
-- url     : https://prove2.me/submissions/5710389f-fb0c-4c62-871a-af2b8317ac40

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.RingTheory.Algebraic.Defs
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_support_finite
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_aeval_pole_le_weighted_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_principal_divisor_positive_eq_poles
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_coordinate_pole_le_weighted
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurvePole_support_subset_coordinate_poles
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (_hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (hN : 0 ≤ N)
    (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F)
    (_hne : MvPolynomial.aeval x F ≠ 0) :
    ({nu : PolynomialCurvePlace E |
      0 < polynomialCurveOrder nu (MvPolynomial.aeval x F)}.Finite ∧
      (∑ᶠ nu : PolynomialCurvePlace E,
        max (polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real) 0) ≤
        N * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w)) := by
  classical
  set f : E := MvPolynomial.aeval x F
  -- Finite positive-order support from full order support
  have hordFin := polynomialCurveOrder_support_finite htrdeg f
  have hposFin : {nu : PolynomialCurvePlace E | 0 < polynomialCurveOrder nu f}.Finite := by
    refine hordFin.subset ?_
    intro nu hnu
    have : (polynomialCurveOrder nu f : Int) ≠ 0 := ne_of_gt hnu
    exact this
  -- Degree-zero comparison of positive and pole parts
  have hdeg := principal_divisor_positive_eq_poles htrdeg f
  -- Pointwise pole bound for the evaluation
  have hpole : ∀ nu, 0 ≤ max (-(polynomialCurveOrder nu f : Real)) 0 ∧
      max (-(polynomialCurveOrder nu f : Real)) 0 ≤
        N * polynomialCurvePole nu x w := by
    intro nu
    refine ⟨le_max_right _ _, ?_⟩
    simpa [f] using polynomial_curve_aeval_pole_le_weighted_height nu x w hw N hN F hF
  -- Finite support of the pole part of f and of weighted poles
  have hpoleFin : Set.Finite {nu | max (-(polynomialCurveOrder nu f : Real)) 0 ≠ 0} := by
    refine hordFin.subset ?_
    intro nu hnu
    have hpos : 0 < max (-(polynomialCurveOrder nu f : Real)) 0 :=
      lt_of_le_of_ne (le_max_right _ _) hnu.symm
    have hneg : 0 < -(polynomialCurveOrder nu f : Real) :=
      (lt_max_iff.mp hpos).resolve_right (lt_irrefl _)
    have : (polynomialCurveOrder nu f : Real) ≠ 0 := by nlinarith
    exact_mod_cast this
  -- Weighted pole support: use order supports of coordinates via the covering + order finite
  -- Simpler: from pointwise, if N*Pole ≠ contribution... actually need Finite {Pole ≠ 0}.
  -- When N = 0, bound is 0. When N > 0, {N*Pole ≠ 0} = {Pole ≠ 0} up to the inequality uses.
  -- Use: support of (N * Pole) sits in pole support; get finiteness from coordinate orders.
  have hWFin : Set.Finite {nu | polynomialCurvePole nu x w ≠ 0} := by
    -- Fall back: every place with Pole ≠ 0 has some coordinate with nonzero order
    -- We already have the subset lemma on the platform; import it.
    have hsub :=
      OAI.PiExponent.FormalInterpolation.polynomialCurvePole_support_subset_coordinate_poles
        x w hw
    have hunion : Set.Finite
        (⋃ j : Fin d, {nu | max (-(polynomialCurveOrder nu (x j) : Real)) 0 ≠ 0}) := by
      refine Set.finite_iUnion fun j => ?_
      refine (polynomialCurveOrder_support_finite htrdeg (x j)).subset ?_
      intro nu hnu
      have hpos : 0 < max (-(polynomialCurveOrder nu (x j) : Real)) 0 :=
        lt_of_le_of_ne (le_max_right _ _) hnu.symm
      have hneg : 0 < -(polynomialCurveOrder nu (x j) : Real) :=
        (lt_max_iff.mp hpos).resolve_right (lt_irrefl _)
      have : (polynomialCurveOrder nu (x j) : Real) ≠ 0 := by nlinarith
      exact_mod_cast this
    exact hunion.subset hsub
  -- Apply finsum comparison to the pole parts, then rewrite via degree zero
  have hcmp :=
    finsum_coordinate_pole_le_weighted N hN
      (fun nu => max (-(polynomialCurveOrder nu f : Real)) 0)
      (fun nu => polynomialCurvePole nu x w)
      hpoleFin hWFin hpole
  have : (∑ᶠ nu, max (polynomialCurveOrder nu f : Real) 0) ≤
      N * (∑ᶠ nu, polynomialCurvePole nu x w) := by
    rw [hdeg]; exact hcmp
  exact ⟨hposFin, this⟩
