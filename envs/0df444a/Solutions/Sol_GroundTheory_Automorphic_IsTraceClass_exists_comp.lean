-- Prove2me | solution 1 for GroundTheory.Automorphic.IsTraceClass.exists_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:58.494651+00:00
-- url     : https://prove2.me/submissions/84d7320f-bf52-47f7-b166-7bb272480868

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_isTraceClass_iff_isHilbertSchmidt_sqrt
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left


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
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ T = A.comp B := by
  obtain ⟨V, -, hVT, -⟩ := exists_polar T
  have hs : IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) :=
    (isTraceClass_iff_isHilbertSchmidt_sqrt T).1 hT
  refine ⟨V.comp (CFC.sqrt (CFC.abs T)), CFC.sqrt (CFC.abs T), hs.comp_left V, hs, ?_⟩
  have hss : (CFC.sqrt (CFC.abs T)).comp (CFC.sqrt (CFC.abs T)) = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
  rw [comp_assoc, hss, hVT]
end IsTraceClass
end GroundTheory.Automorphic
