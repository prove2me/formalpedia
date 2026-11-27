-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:26.759346+00:00
-- url     : https://prove2.me/submissions/e9232489-c5e0-499c-a5c0-faf9dcbfb5f2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_adjoint
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_adjoint


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
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (T†) = starRingEnd ℂ (trace T) := by
  let b := stdHilbertBasis ℂ H
  refine (hT.adjoint.hasSum_trace b).unique ?_
  have hfun : (fun i => ⟪b i, (T†) (b i)⟫_ℂ) = fun i => star ⟪b i, T (b i)⟫_ℂ := by
    ext i; rw [adjoint_inner_right, ← inner_conj_symm]; rfl
  rw [hfun, starRingEnd_apply]
  exact (hT.hasSum_trace b).star
end GroundTheory.Automorphic
