-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_relation_implies_coordinate_nilpotent_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:32:08.176543+00:00
-- url     : https://prove2.me/submissions/f0907ded-8e92-46ba-b248-68a3b93961cc

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_positive_degree_relation_implies_coordinate_nilpotent_v3
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_relation_implies_coordinate_nilpotent_v3

open scoped BigOperators

set_option autoImplicit false

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hcomponents : ∀ f : MvPolynomial (Fin d) ℂ, f ∈ I →
      ∀ r : ℚ, MvPolynomial.weightedHomogeneousComponent w r f ∈ I)
    (i : Fin d) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hpI : Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I) :
    ∃ n : Nat, 0 < n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by
  by_cases hdeg : 0 < p.natDegree
  · exact OAI.PiExponent.FormalInterpolation.positive_degree_relation_implies_coordinate_nilpotent_v3
      w hw I hcomponents i p hp hpI hdeg
  · exact OAI.PiExponent.FormalInterpolation.constant_relation_implies_coordinate_nilpotent_v3
      w hw I hcomponents i p hp hpI hdeg
