-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:31.826829+00:00
-- url     : https://prove2.me/submissions/39273996-03b6-4438-85e5-722e952b42ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_smul


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
theorem _root_.solution (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (c • T) = c * trace T := by
  let b := stdHilbertBasis ℂ H
  refine ((hT.smul c).hasSum_trace b).unique ?_
  have hfun : (fun i => ⟪b i, (c • T) (b i)⟫_ℂ) = fun i => c * ⟪b i, T (b i)⟫_ℂ := by
    ext i; rw [smul_apply, inner_smul_right]
  rw [hfun]
  exact (hT.hasSum_trace b).mul_left c
end GroundTheory.Automorphic
