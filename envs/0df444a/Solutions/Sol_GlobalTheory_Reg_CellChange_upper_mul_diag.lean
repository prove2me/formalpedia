-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.upper_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:12.305305+00:00
-- url     : https://prove2.me/submissions/a54aaf9b-10d7-4443-9ea6-ce3e7b46b4ef

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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) (hc : c.BlockTriangular id) (hv : ∀ i, IsUnit (c i i)) (i : Fin n) :
    IsUnit ((b * c) i i) := by
  have h1 : IsUnit (b * c).det := by
    rw [Matrix.det_mul]
    exact (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu).mul (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag c hc hv)
  rw [Matrix.det_of_upperTriangular (hb.mul hc)] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)
end GlobalTheory.Reg.CellChange
