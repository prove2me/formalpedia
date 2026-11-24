-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.repr_mem_polyOnCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:52.505173+00:00
-- url     : https://prove2.me/submissions/561905c5-d910-490b-b6dc-dce78e25c5fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_eval_adjugate_polyMat
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_repr_cellFrame
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
theorem _root_.solution (b : Frames k V) (i : ι) (v : V i) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => (b' i).repr v a) ∈ polyOnCell b :=
  ⟨∑ c, (polyMat (k := k) (V := V) i).adjugate a c * MvPolynomial.C ((b i).repr v c), fun u => by
    show (cellFrame b u i).repr v a = _
    rw [repr_cellFrame]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MvPolynomial.eval_C (f := u), eval_adjugate_polyMat]⟩
end GlobalTheory.FlagPts.CellCont
