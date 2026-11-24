-- Prove2me | solution 1 for GlobalTheory.FlagPts.toMatrix_cellFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:36.675506+00:00
-- url     : https://prove2.me/submissions/f7ede9f1-02f7-43d6-bc73-938fa731fef4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InjectiveCellMap
import Theorems.Thm_GlobalTheory_FlagPts_cellFrame_apply
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
namespace GlobalTheory.FlagPts
theorem _root_.solution {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    (b i).toMatrix (cellFrame b u i) = uniMat u i := by
  ext a c
  rw [Basis.toMatrix_apply, cellFrame_apply, map_sum]
  simp [Finsupp.single_apply]
end GlobalTheory.FlagPts
