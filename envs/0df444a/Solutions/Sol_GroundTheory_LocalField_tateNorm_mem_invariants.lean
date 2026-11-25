-- Prove2me | solution 1 for GroundTheory.LocalField.tateNorm_mem_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:31.922427+00:00
-- url     : https://prove2.me/submissions/fa3aa503-4b3f-4659-80dc-fe3ae91c86a6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_smul_tateNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}
namespace GroundTheory.LocalField
theorem _root_.solution (x : M) : tateNorm G M x ∈ invariants G M :=
  fun g => smul_tateNorm g x
end GroundTheory.LocalField
