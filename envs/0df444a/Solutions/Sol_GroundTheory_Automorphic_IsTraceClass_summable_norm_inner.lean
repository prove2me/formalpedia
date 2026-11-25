-- Prove2me | solution 1 for GroundTheory.Automorphic.IsTraceClass.summable_norm_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:06.484938+00:00
-- url     : https://prove2.me/submissions/cc785e1a-0cbc-4b90-a1b8-3eb256c26537

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_tsum_enorm_inner_self_le

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
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : Summable fun i => ‖⟪b i, T (b i)⟫_ℂ‖ := by
  have h := ENNReal.summable_toReal ((tsum_enorm_inner_self_le b T).trans_lt hT).ne
  simpa using h
end IsTraceClass
end GroundTheory.Automorphic
