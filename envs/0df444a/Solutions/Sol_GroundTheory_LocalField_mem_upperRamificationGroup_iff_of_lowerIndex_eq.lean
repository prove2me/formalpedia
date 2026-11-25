-- Prove2me | solution 1 for GroundTheory.LocalField.mem_upperRamificationGroup_iff_of_lowerIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:35.622064+00:00
-- url     : https://prove2.me/submissions/9cea72ab-db3f-4801-a509-ef956daaa997

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_herbrandPhi_herbrandPsi
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
theorem _root_.solution {v : ℝ} {σ : L ≃ₐ[K] L} {m : ℕ}
    (h : lowerIndex K L σ = m) :
    σ ∈ upperRamificationGroup K L v ↔ v ≤ herbrandPhi K L ((m : ℝ) - 1) := by
  rw [upperRamificationGroup, mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq h,
    ← le_sub_iff_add_le, ← (herbrandPhi_strictMono (K := K) (L := L)).le_iff_le,
    herbrandPhi_herbrandPsi]
end GroundTheory.LocalField
