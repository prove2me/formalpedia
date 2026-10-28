-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_componentLocalLength_bound_of_minimalPrime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:58:25.516259+00:00
-- url     : https://prove2.me/submissions/57dba6b0-31df-4160-ad71-f23cab555a13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalBasis_card_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_componentLocalLength_bound_of_height

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ f ∈ S, logarithmicDegreeBound w H f)
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A)
    (L : Nat)
    (hlength :
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
          (L : ENat)) :
    (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by
  have hcodim :=
    OAI.PiExponent.FormalInterpolation.coordinateNormalBasis_card_eq_height
      P A hA
  exact OAI.PiExponent.FormalInterpolation.weighted_componentLocalLength_bound_of_height
    w hw H hH S P hminimal hdegree A hcodim L hlength