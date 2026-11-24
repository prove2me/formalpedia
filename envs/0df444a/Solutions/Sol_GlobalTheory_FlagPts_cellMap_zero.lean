-- Prove2me | solution 1 for GlobalTheory.FlagPts.cellMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:14.214845+00:00
-- url     : https://prove2.me/submissions/b699ba6d-f9b9-4ec4-8044-50d6868ee0d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Theorems.Thm_GlobalTheory_FlagPts_cellFrame_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {k V}
namespace GlobalTheory.FlagPts
theorem _root_.solution (b : Frames k V) : cellMap b 0 = b.flags := by
  rw [cellMap, cellFrame_zero]
end GlobalTheory.FlagPts
