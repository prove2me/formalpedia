-- Prove2me | solution 1 for GroundTheory.LocalField.upperRamificationGroup_herbrandPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:48:39.285291+00:00
-- url     : https://prove2.me/submissions/7ee5703b-1b46-4a70-a7c4-01bf6c0c4966

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
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
theorem _root_.solution (u : ℝ) :
    upperRamificationGroup K L (herbrandPhi K L u) = lowerRamificationGroupReal K L u := by
  rw [upperRamificationGroup, herbrandPsi_herbrandPhi]
end GroundTheory.LocalField
