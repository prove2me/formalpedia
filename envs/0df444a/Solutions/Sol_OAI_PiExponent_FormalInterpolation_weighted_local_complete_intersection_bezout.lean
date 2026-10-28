-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T23:56:40.985853+00:00
-- url     : https://prove2.me/submissions/dd491e57-e7f4-4b96-b669-13ada4aacb76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_local_complete_intersection_bezout_height_zero
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_local_complete_intersection_bezout_positive_height

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m k : Nat} (w : Fin (m + 1) -> Rat)
    (hw : forall i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (f : Fin k -> MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (Set.range f)).IsMinimalPrime P)
    (hdegree : forall j, logarithmicDegreeBound w H (f j))
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A)
    (hcard : A.card = P.height)
    (L : Nat)
    (hlength :
      componentLocalLength (Ideal.span (Set.range f)) P = (L : ENat)) :
    (L : Real) * (Finset.prod A fun i => (w i : Real)) <= 2 * H ^ A.card := by
  by_cases hz : P.height = 0
  · exact OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout_height_zero
      w hw H hH f P hminimal hdegree A hA hcard L hlength hz
  · have hpos : 0 < P.height := lt_of_le_of_ne zero_le (Ne.symm hz)
    exact OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout_positive_height
      w hw H hH f P hminimal hdegree A hA hcard L hlength hpos