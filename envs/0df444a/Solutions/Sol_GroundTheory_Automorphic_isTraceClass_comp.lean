-- Prove2me | solution 1 for GroundTheory.Automorphic.isTraceClass_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:51.995585+00:00
-- url     : https://prove2.me/submissions/1b60d5af-8c6c-4231-b4f8-10ee0e526d5d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_two_mul_traceNorm_comp_le

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
theorem _root_.solution {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le A B).trans_lt (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h
end GroundTheory.Automorphic
