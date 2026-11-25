-- Prove2me | solution 1 for GroundTheory.LocalField.isProperMap_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:23.944337+00:00
-- url     : https://prove2.me/submissions/a132278e-a752-4c8a-bd24-8461e371fce4

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
import Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_ord_eq
import Theorems.Thm_GroundTheory_LocalField_isCompact_setOf_ord_eq
import Theorems.Thm_GroundTheory_LocalField_ord_norm
import Theorems.Thm_GroundTheory_LocalField_continuous_normUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos
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
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : IsProperMap (normUnits K L) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_normUnits K L, fun C hC ↦ ?_⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun m : ℤ ↦ {y : Kˣ | ord (y : K) = m})
    isOpen_setOf_ord_eq (fun y _ ↦ Set.mem_iUnion.2 ⟨_, rfl⟩)
  refine IsCompact.of_isClosed_subset
    (t.isCompact_biUnion fun m _ ↦ isCompact_setOf_ord_eq (m / residueDegree K L))
    (hC.isClosed.preimage (continuous_normUnits K L)) ?_
  intro x hx
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine Set.mem_iUnion₂.2 ⟨m, hm, ?_⟩
  simp only [Set.mem_ofPred_eq, coe_normUnits, ord_norm] at hxm ⊢
  have hf : (residueDegree K L : ℤ) ≠ 0 := by exact_mod_cast (residueDegree_pos K L).ne'
  rw [← hxm, Int.mul_ediv_cancel_left _ hf]
end GroundTheory.LocalField
