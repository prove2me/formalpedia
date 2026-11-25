-- Prove2me | solution 1 for GroundTheory.Automorphic.IsTraceClass.hasSum_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:48.687518+00:00
-- url     : https://prove2.me/submissions/b3c5087b-c4fc-4de7-abf3-479f191d8ce2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_exists_comp
import Theorems.Thm_GroundTheory_Automorphic_trace_comp_comm_of_isHilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_hasSum_inner_comp_comm


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
    (b : HilbertBasis ι ℂ H) : HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (trace T) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  have h1 := hasSum_inner_comp_comm b (stdHilbertBasis ℂ H) hA hB
  rw [trace_comp_comm_of_isHilbertSchmidt hA hB]
  exact h1
end IsTraceClass
end GroundTheory.Automorphic
