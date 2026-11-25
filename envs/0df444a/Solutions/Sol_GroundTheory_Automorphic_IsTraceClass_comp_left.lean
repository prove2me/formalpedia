-- Prove2me | solution 1 for GroundTheory.Automorphic.IsTraceClass.comp_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:00.691711+00:00
-- url     : https://prove2.me/submissions/9f5870b5-1e46-4bbb-b3d1-8bc29bd9a3e6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass

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
    IsTraceClass (C.comp T) :=
  (traceNorm_comp_left_le C T).trans_lt (ENNReal.mul_lt_top (by simp) hT)
end IsTraceClass
end GroundTheory.Automorphic
