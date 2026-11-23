-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.upper_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:47.495623+00:00
-- url     : https://prove2.me/submissions/29d9869c-8264-40f5-af36-5cd0884ad537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
import Theorems.Thm_GlobalTheory_isUnit_det_of_upper_of_isUnit_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix
namespace GlobalTheory.Reg.CellChange
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) : b⁻¹.BlockTriangular id ∧ (∀ i, IsUnit (b⁻¹ i i)) ∧ b * b⁻¹ = 1 := by
  have hd := GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu
  have hbi : b⁻¹.BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet b hd
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨hbi, fun i => ?_, Matrix.mul_nonsing_inv _ hd⟩
  have h1 : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hd
  rw [Matrix.det_of_upperTriangular hbi] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)
end GlobalTheory.Reg.CellChange
