-- Prove2me | solution 1 for GroundTheory.Automorphic.traceNorm_adjoint_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:56.807874+00:00
-- url     : https://prove2.me/submissions/5a155a43-d8bd-40b3-8691-3eb022d18e32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_enorm_inner_comm


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
theorem _root_.solution (T : H →L[ℂ] H) : traceNorm (T†) ≤ traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (T†)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc traceNorm (T†) ≤ ∑' i, ‖⟪V (b i), (T†) (b i)⟫_ℂ‖ₑ := traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪ContinuousLinearMap.id ℂ H (b i), T (V (b i))⟫_ℂ‖ₑ := by
        congr 1; ext i
        rw [adjoint_inner_right, enorm_inner_comm, id_apply]
    _ ≤ ‖ContinuousLinearMap.id ℂ H‖ₑ * ‖V‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm T := by simp only [one_mul]
end GroundTheory.Automorphic
