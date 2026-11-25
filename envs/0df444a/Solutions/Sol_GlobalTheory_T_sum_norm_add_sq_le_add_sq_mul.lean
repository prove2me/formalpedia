-- Prove2me | solution 1 for GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:40.286995+00:00
-- url     : https://prove2.me/submissions/bb4b74bc-bbb3-4e1e-a9b5-0a8a094d328c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
import Theorems.Thm_GlobalTheory_sum_norm_add_sq_le_of_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  first | exact @GlobalTheory.sum_norm_add_sq_le_of_bounds | exact GlobalTheory.sum_norm_add_sq_le_of_bounds | (intros; apply GlobalTheory.sum_norm_add_sq_le_of_bounds <;> assumption)
end _root_.GlobalTheory.T
