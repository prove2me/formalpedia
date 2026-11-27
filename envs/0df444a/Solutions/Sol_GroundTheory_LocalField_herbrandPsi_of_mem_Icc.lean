-- Prove2me | solution 1 for GroundTheory.LocalField.herbrandPsi_of_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:50.251458+00:00
-- url     : https://prove2.me/submissions/7b8395a8-4dd5-4d4b-a035-6251e2d6a873

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_herbrandPhi_herbrandPsi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_herbrandPhi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_strictMono
import Theorems.Thm_GroundTheory_LocalField_relIndex_pos_of_finite
import Theorems.Thm_GroundTheory_LocalField_herbrandPhi_of_mem_Icc
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
theorem _root_.solution (n : ℕ) {v : ℝ}
    (hv : v ∈ Set.Icc (herbrandPhi K L n) (herbrandPhi K L (n + 1))) :
    herbrandPsi K L v = n + (v - herbrandPhi K L n) *
      ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup K L 0) : ℝ) := by
  set u := herbrandPsi K L v with hu_def
  have hu : u ∈ Set.Icc (n : ℝ) (n + 1) := by
    constructor
    · rw [← herbrandPsi_herbrandPhi (K := K) (L := L) (n : ℝ)]
      exact (herbrandPsi_strictMono (K := K) (L := L)).monotone hv.1
    · rw [← herbrandPsi_herbrandPhi (K := K) (L := L) ((n : ℝ) + 1)]
      exact (herbrandPsi_strictMono (K := K) (L := L)).monotone hv.2
  have h := herbrandPhi_of_mem_Icc (K := K) (L := L) n hu
  rw [hu_def, herbrandPhi_herbrandPsi] at h
  have hr := relIndex_pos_of_finite (lowerRamificationGroup K L ((n : ℤ) + 1))
    (lowerRamificationGroup K L 0)
  rw [h]
  field_simp
  ring
end GroundTheory.LocalField
