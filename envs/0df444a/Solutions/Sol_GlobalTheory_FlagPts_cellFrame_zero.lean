-- Prove2me | solution 1 for GlobalTheory.FlagPts.cellFrame_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:35.935141+00:00
-- url     : https://prove2.me/submissions/9a17c380-22d2-48d8-88e6-651819fc1751

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Theorems.Thm_GlobalTheory_FlagPts_cellFrame_apply
import Theorems.Thm_GlobalTheory_FlagPts_uniMat_zero
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {k V}
namespace GlobalTheory.FlagPts
theorem _root_.solution (b : Frames k V) : cellFrame b 0 = b := by
  funext i
  ext c
  rw [cellFrame_apply, uniMat_zero]
  simp [Matrix.one_apply]
end GlobalTheory.FlagPts
