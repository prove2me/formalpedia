-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:23:58.931161+00:00
-- url     : https://prove2.me/submissions/531642f9-0df6-4984-9408-007aff9f7c4d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_right
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_exists_comp
import Theorems.Thm_GroundTheory_Automorphic_trace_comp_comm_of_isHilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_right


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
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    trace (C.comp T) = trace (T.comp C) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  calc trace (C.comp (A.comp B)) = trace ((C.comp A).comp B) := by rw [comp_assoc]
    _ = trace (B.comp (C.comp A)) := trace_comp_comm_of_isHilbertSchmidt (hA.comp_left C) hB
    _ = trace ((B.comp C).comp A) := by rw [comp_assoc]
    _ = trace (A.comp (B.comp C)) := trace_comp_comm_of_isHilbertSchmidt (hB.comp_right C) hA
    _ = trace ((A.comp B).comp C) := by rw [comp_assoc]
end GroundTheory.Automorphic
