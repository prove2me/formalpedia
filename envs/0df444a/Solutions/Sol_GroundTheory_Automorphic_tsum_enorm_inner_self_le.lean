-- Prove2me | solution 1 for GroundTheory.Automorphic.tsum_enorm_inner_self_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:05.130263+00:00
-- url     : https://prove2.me/submissions/46f8d80c-216e-42c3-ae97-21a57cf6b718

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass

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
theorem _root_.solution {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ ≤ traceNorm T := by
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ
      = ∑' i, ‖⟪ContinuousLinearMap.id ℂ H (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ :=
        rfl
    _ ≤ ‖ContinuousLinearMap.id ℂ H‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T :=
        tsum_enorm_inner_le b T _ _
    _ ≤ 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm T := by simp only [one_mul]
end GroundTheory.Automorphic
