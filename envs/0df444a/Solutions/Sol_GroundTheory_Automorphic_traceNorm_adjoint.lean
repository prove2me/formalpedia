-- Prove2me | solution 1 for GroundTheory.Automorphic.traceNorm_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:54.096152+00:00
-- url     : https://prove2.me/submissions/3b111374-0db2-4c88-ad49-98dea570584f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_traceNorm_adjoint_le

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
theorem _root_.solution (T : H →L[ℂ] H) : traceNorm (T†) = traceNorm T :=
  le_antisymm (traceNorm_adjoint_le T) (by simpa using traceNorm_adjoint_le (T†))
end GroundTheory.Automorphic
