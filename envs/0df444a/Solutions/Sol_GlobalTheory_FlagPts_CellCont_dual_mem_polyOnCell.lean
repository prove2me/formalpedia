-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.dual_mem_polyOnCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:39.19483+00:00
-- url     : https://prove2.me/submissions/64b571ea-a69d-4cb0-8132-79ab89046455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_map_polyMat
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
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts.CellCont
theorem _root_.solution (b : Frames k V) (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => φ (b' i a)) ∈ polyOnCell b :=
  ⟨∑ l, MvPolynomial.C (φ (b i l)) * polyMat (k := k) (V := V) i l a, fun u => by
    simp only [cellFrame_apply, map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPolynomial.eval_C (f := u), ← map_polyMat u i, Matrix.map_apply, mul_comm]⟩
end GlobalTheory.FlagPts.CellCont
