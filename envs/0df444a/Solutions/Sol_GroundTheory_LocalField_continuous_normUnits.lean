-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:31.776492+00:00
-- url     : https://prove2.me/submissions/3b95a575-e636-41a9-bfad-e2a5fc3cba7c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_continuous_algebraNorm
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


attribute [local simp] GroundTheory.LocalField.coe_normUnits

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : Continuous (normUnits K L) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_algebraNorm K L).comp Units.continuous_val, ?_⟩
  have h : (fun x : Lˣ ↦ (((normUnits K L x)⁻¹ : Kˣ) : K)) =
      fun x ↦ Algebra.norm K ((x⁻¹ : Lˣ) : L) := by
    funext x
    rw [← map_inv, coe_normUnits]
  rw [h]
  exact (continuous_algebraNorm K L).comp Units.continuous_coe_inv
end GroundTheory.LocalField
