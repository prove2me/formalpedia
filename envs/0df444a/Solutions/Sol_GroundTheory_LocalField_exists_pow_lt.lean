-- Prove2me | solution 1 for GroundTheory.LocalField.exists_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:12.717064+00:00
-- url     : https://prove2.me/submissions/f1570bbb-57c3-42a0-a260-a959eb3ebb93

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
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
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hz : z ≠ 0 := by rintro rfl; simp at hγ
  refine ⟨max 1 (ord z + 1).toNat, le_max_left _ _, ?_⟩
  rw [← map_pow, ← normalizedValuation_lt_iff, map_pow, normalizedValuation_uniformizer hϖ,
    normalizedValuation_eq_exp_ord hz, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_lt_neg_iff]
  have := le_max_right 1 (ord z + 1).toNat
  omega
end GroundTheory.LocalField
