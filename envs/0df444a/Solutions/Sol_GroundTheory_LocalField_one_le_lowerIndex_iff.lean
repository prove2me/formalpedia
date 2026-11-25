-- Prove2me | solution 1 for GroundTheory.LocalField.one_le_lowerIndex_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:47.042326+00:00
-- url     : https://prove2.me/submissions/21f708c3-9a78-422e-b212-e9bba94ff1c9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_natCast_iff_lowerIndex
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_one
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
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.lowerIndex_one

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {σ : L ≃ₐ[K] L} :
    1 ≤ lowerIndex K L σ ↔ σ ∈ lowerRamificationGroup K L 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, mem_lowerRamificationGroup_natCast_iff_lowerIndex]
  simp
end GroundTheory.LocalField
