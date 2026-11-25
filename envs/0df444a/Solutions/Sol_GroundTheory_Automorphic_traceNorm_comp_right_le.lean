-- Prove2me | solution 1 for GroundTheory.Automorphic.traceNorm_comp_right_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:58.189712+00:00
-- url     : https://prove2.me/submissions/a59915ac-ec72-4ce7-ac0a-43ca99b0b4f6

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
theorem _root_.solution (T C : H →L[ℂ] H) :
    traceNorm (T.comp C) ≤ ‖C‖ₑ * traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (T.comp C)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc traceNorm (T.comp C) ≤ ∑' i, ‖⟪V (b i), (T.comp C) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪V (b i), T (C (b i))⟫_ℂ‖ₑ := rfl
    _ ≤ ‖V‖ₑ * ‖C‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ 1 * ‖C‖ₑ * traceNorm T := by gcongr
    _ = ‖C‖ₑ * traceNorm T := by rw [one_mul]
end GroundTheory.Automorphic
