-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_zero_preserves_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T09:32:06.432989+00:00
-- url     : https://prove2.me/submissions/3bd3b673-357a-497e-9b9c-500f61829f2d

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_X_pderiv_support_v2
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_pderiv_support_v2
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_add_support_v2

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F) :
    logarithmicDegreeBound w N (logarithmicFrameDerivative (0 : Fin (m + 1)) F) := by
  classical
  have hsum (s : Finset (Fin m)) :
      logarithmicDegreeBound w N
        (s.sum (fun j => MvPolynomial.pderiv j.succ F)) := by
    induction s using Finset.induction_on with
    | empty =>
        simp [logarithmicDegreeBound]
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact logarithmicDegreeBound_add_support_v2 w N _ _
          (logarithmicDegreeBound_pderiv_support_v2 w hw N F hF j.succ) ih
  change logarithmicDegreeBound w N
    (MvPolynomial.X 0 * MvPolynomial.pderiv 0 F +
      ∑ j : Fin m, MvPolynomial.pderiv j.succ F)
  exact logarithmicDegreeBound_add_support_v2 w N _ _
    (logarithmicDegreeBound_X_pderiv_support_v2 w hw N F hF 0)
    (hsum Finset.univ)
