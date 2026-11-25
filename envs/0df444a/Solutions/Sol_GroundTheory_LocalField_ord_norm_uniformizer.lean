-- Prove2me | solution 1 for GroundTheory.LocalField.ord_norm_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:50:13.784982+00:00
-- url     : https://prove2.me/submissions/476e4bb5-cce9-481d-aa3c-2cfdbae7ad0d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_pow
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_ord_algebraMap_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_norm_units
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
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
theorem _root_.solution {π : 𝒪[L]} (hπ : Irreducible π) :
    ord (Algebra.norm K (π : L)) = residueDegree K L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖL : algebraMap K L (ϖ : K) ≠ 0 := by simpa using hϖ0
  have h := ord_norm_units (K := K) hπ (Units.mk0 _ hϖL)
  rw [Units.val_mk0, Algebra.norm_algebraMap, ord_pow hϖ0, ord_uniformizer hϖ,
    ord_algebraMap_uniformizer hϖ, ← ramificationIndex_mul_residueDegree K L] at h
  have he : (ramificationIndex K L : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos K L).ne'
  push_cast at h
  exact (mul_left_cancel₀ he (by linear_combination h)).symm
end GroundTheory.LocalField
