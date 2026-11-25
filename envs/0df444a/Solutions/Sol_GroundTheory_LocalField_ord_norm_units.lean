-- Prove2me | solution 1 for GroundTheory.LocalField.ord_norm_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:54.957773+00:00
-- url     : https://prove2.me/submissions/6ad8eb14-48ff-4ea1-9573-725062740946

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zpow
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_ord_unitsOfIntProd
import Theorems.Thm_GroundTheory_LocalField_unitsOfIntProd_eq
import Theorems.Thm_GroundTheory_LocalField_normUnits_unitsIncl
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_unit
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
attribute [local simp] GroundTheory.LocalField.ord_zero

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {π : 𝒪[L]} (hπ : Irreducible π) (x : Lˣ) :
    ord (Algebra.norm K (x : L)) = ord (x : L) * ord (Algebra.norm K (π : L)) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := (unitsOfIntProd_bijective hπ).2 x
  rw [ord_unitsOfIntProd, ← coe_normUnits, unitsOfIntProd_eq, map_mul, map_zpow,
    normUnits_unitsIncl, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_unitsIncl,
    ord_mul (zpow_ne_zero _ (Units.ne_zero _)) (by simp), ord_zpow (Units.ne_zero _), ord_unit,
    coe_normUnits, coe_uniformizerUnit]
  ring
end GroundTheory.LocalField
