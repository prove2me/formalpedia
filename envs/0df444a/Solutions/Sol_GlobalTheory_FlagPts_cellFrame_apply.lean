-- Prove2me | solution 1 for GlobalTheory.FlagPts.cellFrame_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:49.232773+00:00
-- url     : https://prove2.me/submissions/1a43b8b2-345d-4cdc-be1c-5b6b4aa0c6c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
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
theorem _root_.solution (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) (c : Fin (finrank k (V i))) :
    cellFrame b u i c = ∑ a, uniMat u i a c • b i a := by
  simp [cellFrame, Matrix.toLin_self]
end GlobalTheory.FlagPts
