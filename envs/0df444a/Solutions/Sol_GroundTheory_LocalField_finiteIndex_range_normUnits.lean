-- Prove2me | solution 1 for GroundTheory.LocalField.finiteIndex_range_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:38.534795+00:00
-- url     : https://prove2.me/submissions/510d42cb-fea6-4895-8c0d-9239230497a1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_unitsOfIntProd_eq
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltrationUnits_le_range_normUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_symm_apply
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
variable [Algebra.IsSeparable K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : (normUnits K L).range.FiniteIndex := by
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_range_normUnits K L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set d := Module.finrank K L with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  let P : Subgroup (Multiplicative ℤ × 𝒪[K]ˣ) :=
    (AddSubgroup.zmultiples (d : ℤ)).toSubgroup.prod (unitFiltration K n)
  have hP : P.index ≠ 0 := by
    rw [Subgroup.index_prod, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
    exact mul_ne_zero (by simpa using hd0) (unitFiltration K n).index_ne_zero_of_finite
  have hle : P.comap (unitsEquivIntProd hϖ).toMonoidHom ≤ (normUnits K L).range := by
    intro x hx
    simp only [Subgroup.mem_comap, Subgroup.mem_prod, MulEquiv.coe_toMonoidHom, P] at hx
    obtain ⟨h1, h2⟩ := hx
    set p := unitsEquivIntProd hϖ x with hp
    have hxp : x = unitsOfIntProd hϖ (p.1, p.2) := by
      rw [← unitsEquivIntProd_symm_apply, Prod.mk.eta, hp, MulEquiv.symm_apply_apply]
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp ((Multiplicative.mem_toSubgroup _ _).mp h1)
    rw [hxp, unitsOfIntProd_eq, ← hj, smul_eq_mul, mul_comm j, zpow_mul, zpow_natCast]
    refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ (MonoidHom.mem_range.mpr ⟨Units.map
      (algebraMap K L : K →* L) (uniformizerUnit hϖ), ?_⟩) _) (hn (Subgroup.mem_map.mpr ⟨_, h2, rfl⟩))
    ext
    simp [Algebra.norm_algebraMap, hd]
  have : (P.comap (unitsEquivIntProd hϖ).toMonoidHom).FiniteIndex := by
    constructor
    rw [Subgroup.index_comap_of_surjective _ (unitsEquivIntProd hϖ).surjective]
    exact hP
  exact Subgroup.finiteIndex_of_le hle
end GroundTheory.LocalField
