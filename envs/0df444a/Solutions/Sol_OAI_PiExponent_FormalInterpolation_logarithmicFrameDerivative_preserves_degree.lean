-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_preserves_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T09:06:56.535988+00:00
-- url     : https://prove2.me/submissions/9590aab4-5103-49a1-9122-95b380bbdf20

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_pderiv
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameDerivative_zero_preserves_degree

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (i : Fin (m + 1)) :
    logarithmicDegreeBound w N (logarithmicFrameDerivative i F) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact logarithmicFrameDerivative_zero_preserves_degree w hw N F hF
  · simpa [logarithmicFrameDerivative] using
      logarithmicDegreeBound_pderiv w hw N F hF j.succ