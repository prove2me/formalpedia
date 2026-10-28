-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_coordinate_component_local_length_upper_from_multiplicity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T20:55:46.754611+00:00
-- url     : https://prove2.me/submissions/1006f71d-f6c2-4e55-a8f9-1b5fd140da43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_componentLocalLength_finite_of_minimalPrime
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_componentLocalLength_bound
import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ f ∈ S, logarithmicDegreeBound w H f)
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    ∃ L : Nat,
      componentLocalLength
          (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
        (L : ENat) ∧
      (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by
  obtain ⟨L, hlength⟩ :=
    OAI.PiExponent.FormalInterpolation.componentLocalLength_finite_of_minimalPrime
      S P hminimal
  refine ⟨L, hlength, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.weighted_componentLocalLength_bound
    w hw H hH S P hminimal hdegree A hA L hlength