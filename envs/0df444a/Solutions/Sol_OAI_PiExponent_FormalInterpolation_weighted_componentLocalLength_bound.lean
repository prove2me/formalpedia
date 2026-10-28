-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_componentLocalLength_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T21:23:50.914518+00:00
-- url     : https://prove2.me/submissions/205106c5-a813-4134-ba05-d6c93e35ab2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_normal_basis_card_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_generic_local_slice_for_weighted_bezout
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_local_complete_intersection_bezout

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
  have hcard : A.card = P.height :=
    coordinate_normal_basis_card_eq_height P A hA
  obtain ⟨f, hfI, hfdegree, hminimalF, M, hlengthF, hLM⟩ :=
    generic_local_slice_for_weighted_bezout
      w hw H hH S P hminimal hdegree A hcard L hlength
  have hbezout :=
    weighted_local_complete_intersection_bezout
      w hw H hH f P hminimalF hfdegree A hA hcard M hlengthF
  have hprod : 0 ≤ ∏ i ∈ A, (w i : Real) :=
    Finset.prod_nonneg fun i hi => le_of_lt (hw i)
  exact le_trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hLM) hprod)
    hbezout