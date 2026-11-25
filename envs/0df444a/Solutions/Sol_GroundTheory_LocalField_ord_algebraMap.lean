-- Prove2me | solution 1 for GroundTheory.LocalField.ord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:02.893997+00:00
-- url     : https://prove2.me/submissions/df1323dc-ea91-45e1-806b-20596a39d29f

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
import Theorems.Thm_GroundTheory_LocalField_ord_algebraMap_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
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
theorem _root_.solution (a : K) : ord (algebraMap K L a) = ramificationIndex K L * ord a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨⟨n, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 (Units.mk0 a ha)
  have ha' : a = (ϖ : K) ^ n.toAdd * ((u : 𝒪[K]) : K) := by
    rw [← coe_unitsOfIntProd hϖ, hx, Units.val_mk0]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖL : algebraMap K L (ϖ : K) ≠ 0 := by simpa using hϖ0
  have hu : algebraMap K L ((u : 𝒪[K]) : K) =
      (((Units.map (algebraMap 𝒪[K] 𝒪[L]).toMonoidHom u : 𝒪[L]ˣ) : 𝒪[L]) : L) := rfl
  rw [ha', map_mul, map_zpow₀, ord_mul (zpow_ne_zero _ hϖL) (by rw [hu]; simp), ord_zpow hϖL,
    ord_algebraMap_uniformizer hϖ, hu, ord_unit, ord_mul (zpow_ne_zero _ hϖ0) (by simp),
    ord_zpow hϖ0, ord_uniformizer hϖ, ord_unit]
  ring
end GroundTheory.LocalField
