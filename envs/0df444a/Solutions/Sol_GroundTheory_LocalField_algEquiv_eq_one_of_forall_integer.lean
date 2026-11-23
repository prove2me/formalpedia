-- Prove2me | solution 1 for GroundTheory.LocalField.algEquiv_eq_one_of_forall_integer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:55.333568+00:00
-- url     : https://prove2.me/submissions/4a4f2020-9578-4282-85e1-3ded80b99e91

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
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



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝒪[L], integerAlgEquiv K L σ x = x) : σ = 1 := by
  ext y
  rw [AlgEquiv.one_apply]
  by_cases hy : valuation L y ≤ 1
  · exact congrArg Subtype.val (h ⟨y, hy⟩)
  · have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hinv : valuation L y⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hy))
    have := congrArg Subtype.val (h ⟨y⁻¹, hinv⟩)
    simp only [coe_integerAlgEquiv_apply, map_inv₀] at this
    exact inv_injective this
end GroundTheory.LocalField
