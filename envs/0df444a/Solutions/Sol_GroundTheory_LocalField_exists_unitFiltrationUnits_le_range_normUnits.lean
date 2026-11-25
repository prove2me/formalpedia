-- Prove2me | solution 1 for GroundTheory.LocalField.exists_unitFiltrationUnits_le_range_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:23:44.401819+00:00
-- url     : https://prove2.me/submissions/6d71a621-58c3-40e8-b1ad-26e845517648

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
import Theorems.Thm_GroundTheory_LocalField_coe_norm_integer
import Theorems.Thm_GroundTheory_LocalField_exists_norm_one_add_smul_eq
import Theorems.Thm_GroundTheory_LocalField_exists_trace_integer_ne_zero
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
variable [Algebra.IsSeparable K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ n, unitFiltrationUnits K n ≤ (normUnits K L).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨z, hz⟩ := exists_trace_integer_ne_zero K L
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz hϖ
  obtain ⟨ε, hε⟩ := hk.symm
  refine ⟨2 * k + 1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hdvd : ϖ ^ (2 * k + 1) ∣ 1 - (a : 𝒪[K]) := by
    rw [← dvd_neg, neg_sub]
    exact (mem_maximalIdeal_pow_iff hϖ).mp ha
  obtain ⟨r, hr⟩ := exists_norm_one_add_smul_eq z hϖ k ε hε.symm a hdvd
  have hN := coe_norm_integer (K := K) (1 + r • z)
  rw [hr] at hN
  have hne : ((1 + r • z : 𝒪[L]) : L) ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hN
    simp at hN
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  rw [coe_normUnits, Units.val_mk0, ← hN, coe_unitsIncl]
end GroundTheory.LocalField
