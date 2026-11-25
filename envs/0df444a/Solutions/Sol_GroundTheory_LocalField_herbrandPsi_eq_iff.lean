-- Prove2me | solution 1 for GroundTheory.LocalField.herbrandPsi_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:41.000859+00:00
-- url     : https://prove2.me/submissions/a58c7095-c470-4b0e-b910-3a01752b0f7d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_herbrandPhiOrderIso_apply
import Theorems.Thm_GroundTheory_LocalField_herbrandPhi_herbrandPsi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_herbrandPhi
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_inv
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_one
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.lowerIndex_inv
attribute [local simp] GroundTheory.LocalField.lowerIndex_one
attribute [local simp] GroundTheory.LocalField.lowerIndex_restrictScalars
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.herbrandPhiOrderIso_apply
attribute [local simp] GroundTheory.LocalField.herbrandPhi_herbrandPsi
attribute [local simp] GroundTheory.LocalField.herbrandPsi_herbrandPhi

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Filter Topology MeasureTheory
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {u v : ℝ} : herbrandPsi K L v = u ↔ herbrandPhi K L u = v := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp
end GroundTheory.LocalField
