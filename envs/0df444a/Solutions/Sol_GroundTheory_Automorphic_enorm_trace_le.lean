-- Prove2me | solution 1 for GroundTheory.Automorphic.enorm_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:08:55.191431+00:00
-- url     : https://prove2.me/submissions/f7761889-32e7-4af1-8f05-d4082232a0b1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace
import Theorems.Thm_GroundTheory_Automorphic_tsum_enorm_inner_self_le
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_summable_norm_inner

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
theorem _root_.solution (T : H →L[ℂ] H) : ‖trace T‖ₑ ≤ traceNorm T := by
  by_cases hT : IsTraceClass T
  · let b := stdHilbertBasis ℂ H
    have hs := hT.summable_norm_inner b
    calc ‖trace T‖ₑ = ENNReal.ofReal ‖trace T‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑' i, ‖⟪b i, T (b i)⟫_ℂ‖) :=
          ENNReal.ofReal_le_ofReal ((hT.hasSum_trace b).norm_le_of_bounded hs.hasSum fun _ => le_rfl)
      _ = ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm]
      _ ≤ traceNorm T := tsum_enorm_inner_self_le b T
  · rw [IsTraceClass, not_lt, top_le_iff] at hT
    rw [hT]; exact le_top
end GroundTheory.Automorphic
