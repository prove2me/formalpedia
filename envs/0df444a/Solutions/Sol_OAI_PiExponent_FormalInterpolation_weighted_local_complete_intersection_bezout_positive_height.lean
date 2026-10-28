-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout_positive_height
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:05:06.28072+00:00
-- url     : https://prove2.me/submissions/0a7af835-77f5-40e9-aadf-71cde2a19f61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_generic_slice_linear_combinations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_local_slice_bezout
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m k : Nat} (w : Fin (m + 1) -> Rat)
    (hw : forall i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (f : Fin k -> MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal : (Ideal.span (Set.range f)).IsMinimalPrime P)
    (hdegree : forall j, logarithmicDegreeBound w H (f j))
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A)
    (hcard : A.card = P.height)
    (L : Nat)
    (hlength : componentLocalLength (Ideal.span (Set.range f)) P = (L : ENat))
    (hpos : 0 < P.height) :
    (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by
  rcases generic_slice_linear_combinations w hw H hH f P hminimal hdegree
      A hcard A.card (by exact hcard) L hlength hpos with
    ⟨g, M, hcomb, hdegree_g, hrad, hlength_g, hLM⟩
  have hbez := weighted_local_slice_bezout w hw H hH g P A hcard
      (by exact hcard) hrad hdegree_g hA M hlength_g hpos
  have hprod : 0 < ∏ i ∈ A, (w i : Real) :=
    Finset.prod_pos fun i hi => hw i
  have hle : (L : Real) * (∏ i ∈ A, (w i : Real)) ≤
      (M : Real) * (∏ i ∈ A, (w i : Real)) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hLM) (le_of_lt hprod)
  exact hle.trans hbez
