-- Prove2me | solution 1 for GlobalTheory.T.ray_data_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:34.639423+00:00
-- url     : https://prove2.me/submissions/4d9fcbc4-fce7-4f5c-a5b0-0a60f46253cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonemptyStatement
import Theorems.Thm_GlobalTheory_Mem_RayEx_nonempty_rayData


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → Nonempty (RayData K M) := by
  first | exact @GlobalTheory.Mem.RayEx.nonempty_rayData | exact GlobalTheory.Mem.RayEx.nonempty_rayData | (intros; apply GlobalTheory.Mem.RayEx.nonempty_rayData <;> assumption)
end _root_.GlobalTheory.T
