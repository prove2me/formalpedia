-- Prove2me | solution 1 for GroundTheory.LocalField.enatMin_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:33.637918+00:00
-- url     : https://prove2.me/submissions/9811500c-01bc-4c89-8af3-c3c07bdcb3f1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
import Theorems.Thm_GroundTheory_LocalField_herbrandPhiOrderIso_apply
import Theorems.Thm_GroundTheory_LocalField_herbrandPhi_herbrandPsi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_herbrandPhi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_zero
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_inv
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_one
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_upperRamificationGroup_herbrandPhi
import Theorems.Thm_GroundTheory_LocalField_upperRamificationGroup_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.herbrandPhiOrderIso_apply
attribute [local simp] GroundTheory.LocalField.herbrandPhi_herbrandPsi
attribute [local simp] GroundTheory.LocalField.herbrandPsi_herbrandPhi
attribute [local simp] GroundTheory.LocalField.herbrandPsi_zero
attribute [local simp] GroundTheory.LocalField.lowerIndex_inv
attribute [local simp] GroundTheory.LocalField.lowerIndex_one
attribute [local simp] GroundTheory.LocalField.lowerIndex_restrictScalars
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.LocalField.upperRamificationGroup_herbrandPhi
attribute [local simp] GroundTheory.LocalField.upperRamificationGroup_zero



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
namespace GroundTheory.LocalField
theorem _root_.solution (n N : ℕ∞) (a : ℝ) : enatMin (min n N) a = enatMin n (enatMin N a) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
    induction N using ENat.recTopCoe with
    | top => simp
    | coe l =>
      rw [← (Nat.mono_cast (α := ℕ∞)).map_min, enatMin_coe, enatMin_coe, enatMin_coe, Nat.cast_min,
        min_assoc]
end GroundTheory.LocalField
