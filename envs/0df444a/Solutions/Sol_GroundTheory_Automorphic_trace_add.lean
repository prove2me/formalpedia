-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:15.950852+00:00
-- url     : https://prove2.me/submissions/c2798cc6-93c0-426a-801d-2093e8d25cb7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add


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
theorem _root_.solution {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by
  let b := stdHilbertBasis ℂ H
  refine ((hS.add hT).hasSum_trace b).unique ?_
  convert (hS.hasSum_trace b).add (hT.hasSum_trace b) using 1
  ext i
  rw [add_apply, inner_add_right]
end GroundTheory.Automorphic
