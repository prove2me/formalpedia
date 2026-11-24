-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.regFns_le_polyOnCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:48:34.557733+00:00
-- url     : https://prove2.me/submissions/96738159-46d8-4c51-8735-58d676aac76c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_dual_mem_polyOnCell
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_repr_mem_polyOnCell

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
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts.CellCont
theorem _root_.solution (b : Frames k V) : regFns k V ≤ polyOnCell b := by
  refine Algebra.adjoin_le ?_
  rintro f (⟨i, φ, a, rfl⟩ | ⟨i, v, a, rfl⟩)
  · exact dual_mem_polyOnCell b i φ a
  · exact repr_mem_polyOnCell b i v a
end GlobalTheory.FlagPts.CellCont
