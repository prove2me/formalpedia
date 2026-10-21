-- Prove2me | solution 1 for KAdaptability.PolicyCount.conservative_approximation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:19:15.346593+00:00
-- url     : https://prove2.me/submissions/3867646f-aa37-403d-b46d-0f1ae06c06ab

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_PO
import Definitions.Def_KAdaptability_PolicyCount_POK

set_option autoImplicit false
open Matrix KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

theorem solution (P : Problem N M L nQ R) (K : ℕ) :
    P.optPO ≤ P.optPOK K := by
  unfold Problem.optPOK
  refine le_iInf fun x => le_iInf fun ys => le_iInf fun hf => ?_
  refine le_trans (iInf₂_le x hf.1) ?_
  unfold Problem.objPO Problem.objPOK
  refine iSup₂_mono fun ξ hξ => ?_
  refine add_le_add le_rfl ?_
  refine le_iInf fun k => ?_
  exact (iInf₂_le (ys k) (hf.2 k).1).trans (iInf_le _ (hf.2 k).2)
