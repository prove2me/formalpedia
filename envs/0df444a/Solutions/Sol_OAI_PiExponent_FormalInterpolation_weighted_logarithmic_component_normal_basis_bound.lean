-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_logarithmic_component_normal_basis_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:14:02.689354+00:00
-- url     : https://prove2.me/submissions/305d8e0d-e783-4477-98b4-f78999325b25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_logarithmic_component_normal_basis_factorial_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_interpolationSeparationConstant_dominates_factorial_factor

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ f ∈ S, logarithmicDegreeBound w (N : Real) f)
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word <
        ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
      logarithmicFrameWord word f ∈ P) :
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      coordinateNormalBasisAtPrime P A →
      logarithmicNormalBasisAtPrime P B →
      (∏ i ∈ A, (w i : Real)) ≤
        interpolationSeparationConstant m sigma * (∏ i ∈ B, (v i : Real)) := by
  intro A B hcard hA hB
  have hstrong := weighted_logarithmic_component_normal_basis_factorial_bound
    w v sigma hsigma hw hv N hN S P hP hY hminimal hdegree hwords A B hcard hA hB
  have hk : A.card ≤ m + 1 := by
    simpa using (Finset.card_le_univ A)
  have hfactor := interpolationSeparationConstant_dominates_factorial_factor
    m A.card hk sigma hsigma
  have hprod : 0 ≤ ∏ i ∈ B, (v i : Real) := by
    exact Finset.prod_nonneg fun i hi => (hv i).le
  exact le_trans hstrong (mul_le_mul_of_nonneg_right hfactor hprod)
