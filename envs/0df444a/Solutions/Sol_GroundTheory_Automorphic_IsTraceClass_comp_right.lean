-- Prove2me | solution 1 for GroundTheory.Automorphic.IsTraceClass.comp_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:33:57.736994+00:00
-- url     : https://prove2.me/submissions/0c9d2191-4037-4a34-aca9-744ff8abf11c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_traceNorm_comp_right_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace GroundTheory.Automorphic
namespace IsTraceClass
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    IsTraceClass (T.comp C) :=
  (traceNorm_comp_right_le T C).trans_lt (ENNReal.mul_lt_top (by simp) hT)
end IsTraceClass
end GroundTheory.Automorphic
