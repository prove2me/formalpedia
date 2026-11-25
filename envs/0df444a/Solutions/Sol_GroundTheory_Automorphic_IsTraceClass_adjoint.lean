-- Prove2me | solution 1 for GroundTheory.Automorphic.IsTraceClass.adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:25.294396+00:00
-- url     : https://prove2.me/submissions/1e1074a0-1fe0-456f-b64c-f3d548157bc6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_traceNorm_adjoint

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
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (T†) := by
  rw [IsTraceClass, traceNorm_adjoint]; exact hT
end IsTraceClass
end GroundTheory.Automorphic
