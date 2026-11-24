-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.map_polyMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:14.693479+00:00
-- url     : https://prove2.me/submissions/7044228d-34ed-45aa-941e-26d76ff16c1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
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
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts.CellCont
theorem _root_.solution (u : AffPts k (CellIdx k V)) (i : ι) :
    (polyMat (k := k) (V := V) i).map (MvPolynomial.eval u) = uniMat u i := by
  ext a c
  simp only [Matrix.map_apply, polyMat, uniMat]
  split_ifs
  · exact map_one _
  · exact MvPolynomial.eval_X (f := u) _
  · exact map_zero _
end GlobalTheory.FlagPts.CellCont
