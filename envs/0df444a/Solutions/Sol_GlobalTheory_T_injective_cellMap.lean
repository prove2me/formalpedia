-- Prove2me | solution 1 for GlobalTheory.T.injective_cellMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:14:58.34436+00:00
-- url     : https://prove2.me/submissions/52235d03-ff1c-4aac-aaa9-448d25c90f76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InjectiveCellMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InjectiveCellMapStatement
import Theorems.Thm_GlobalTheory_FlagPts_cellMap_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Function.Injective (cellMap b) := by
  first | exact @GlobalTheory.FlagPts.cellMap_injective | exact GlobalTheory.FlagPts.cellMap_injective | (intros; apply GlobalTheory.FlagPts.cellMap_injective <;> assumption)
end _root_.GlobalTheory.T
