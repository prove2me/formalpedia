-- Prove2me | solution 2 for GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:45.867965+00:00
-- url     : https://prove2.me/submissions/92178c6c-9b84-4261-8be8-38abf9062534

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormHasSumSubFinsetSumLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormHasSumSubFinsetSumLeStatement
import Theorems.Thm_GlobalTheory_norm_hasSum_sub_finset_sum_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  first | exact @GlobalTheory.norm_hasSum_sub_finset_sum_le | exact GlobalTheory.norm_hasSum_sub_finset_sum_le | (intros; apply GlobalTheory.norm_hasSum_sub_finset_sum_le <;> assumption)
end _root_.GlobalTheory.T
