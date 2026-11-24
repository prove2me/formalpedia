-- Prove2me | solution 1 for GlobalTheory.FlagPts.cellMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:13.473322+00:00
-- url     : https://prove2.me/submissions/b6a4b47b-4200-4d15-a475-185267adda09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InjectiveCellMap
import Theorems.Thm_GlobalTheory_FlagPts_toMatrix_cellFrame
import Theorems.Thm_GlobalTheory_FlagPts_uniMat_apply_of_lt
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
theorem _root_.solution (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Function.Injective (cellMap b) := by
  intro u u' h
  have key : ∀ i, uniMat u i = uniMat u' i := by
    intro i
    have hflag : (cellFrame b u i).flag = (cellFrame b u' i).flag :=
      congrArg FullFlag.sub (congrFun h i)
    set B := cellFrame b u i
    set B' := cellFrame b u' i
    set Y := B.toMatrix B'
    have hmul : uniMat u i * Y = uniMat u' i := by
      rw [← toMatrix_cellFrame b u i, ← toMatrix_cellFrame b u' i, Basis.toMatrix_mul_toMatrix]
    have hup : ∀ j c, c < j → Y j c = 0 := by
      intro j c hcj
      have hm : B' c ∈ B'.flag c.succ := B'.self_mem_flag Fin.castSucc_lt_succ
      rw [← hflag] at hm
      exact (mem_basis_flag_iff B _ _).1 hm j (Fin.succ_le_castSucc_iff.mpr hcj)
    have hdet : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
    have hY : Y = (uniMat u i)⁻¹ * uniMat u' i := by
      rw [← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hlow : ∀ j c, j < c → Y j c = 0 := by
      letI := (uniMat u i).invertibleOfIsUnitDet hdet
      have h1 := Matrix.blockTriangular_inv_of_blockTriangular (uniMat_blockTriangular u i)
      have h2 := h1.mul (uniMat_blockTriangular u' i)
      intro j c hjc
      rw [hY]
      exact h2 (by simpa using hjc)
    have hdiag : ∀ c, Y c c = 1 := by
      intro c
      have := congrFun (congrFun hmul c) c
      rw [Matrix.mul_apply, Finset.sum_eq_single c, uniMat_apply_self, uniMat_apply_self, one_mul] at this
      · exact this
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [hlow j c hj, mul_zero]
        · rw [hup j c hj, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    have hY1 : Y = 1 := by
      ext j c
      rcases lt_trichotomy j c with hjc | rfl | hjc
      · rw [hlow j c hjc, Matrix.one_apply_ne hjc.ne]
      · rw [hdiag, Matrix.one_apply_eq]
      · rw [hup j c hjc, Matrix.one_apply_ne hjc.ne']
    rw [← hmul, hY1, Matrix.mul_one]
  funext x
  obtain ⟨i, ⟨a, c⟩, hac⟩ := x
  have := congrFun (congrFun (key i) a) c
  rwa [uniMat_apply_of_lt u i hac, uniMat_apply_of_lt u' i hac] at this
end GlobalTheory.FlagPts
