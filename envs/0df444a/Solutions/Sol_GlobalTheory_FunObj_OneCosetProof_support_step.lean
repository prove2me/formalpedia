-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.support_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:51:07.326208+00:00
-- url     : https://prove2.me/submissions/1976095c-0668-4ff8-a829-262240131c96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_frame_mul
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moveArgs_theta
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_downMap_eq
import Theorems.Thm_GlobalTheory_FunObj_fill_theta
import Theorems.Thm_GlobalTheory_FunObj_moved_false
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution (hs : 1 ≤ G.s) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup) (x : ColArgs G)
    (y : RowArgs G) (v : Vars G) (h : moved G false g T (fill hs x y v) ≠ 0) (j : Fin (G.m - 1)) (r s) :
    (((frameGL (tgt_eq hs j) (g (G.m, j + 1)))⁻¹).val * stepPt (x j) (v j) *
      (frameGL (src_eq hs j) (g (G.m, j))).val) r s ∈ 𝒪[k] := by
  have hb : Edge.theta G.m (j : ℕ) ∈ oppositePath G.m := by
    simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse]
    right
    exact ⟨j, by have := j.isLt; omega, rfl⟩
  have hT' : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    rw [moved_false] at h
    exact right_ne_zero_of_mul h
  have hm : G.moveArgs .one g (fill hs x y v) (.theta G.m j) ∈ matLat _ (stdLat k _) := by
    by_contra hc
    exact hT' (hT.2.1 _ _ hb hc)
  rw [moveArgs_theta, fill_theta, Matrix.transpose_transpose, downMap_eq hs, frame_mul, mem_matLat_stdLat] at hm
  have := hm (frame (src_eq hs j) s) (frame (tgt_eq hs j) r)
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using this
end GlobalTheory.FunObj.OneCosetProof
