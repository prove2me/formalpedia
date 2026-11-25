-- Prove2me | solution 1 for GroundTheory.LocalField.isCompact_unitFiltrationUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:41.924531+00:00
-- url     : https://prove2.me/submissions/08662dbd-3dcd-4117-a6ea-f97b3e6b0131

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_valuation_lt
import Theorems.Thm_GroundTheory_LocalField_val_image_unitFiltrationUnits_zero
import Theorems.Thm_GroundTheory_LocalField_val_image_unitFiltrationUnits
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
theorem _root_.solution (n : ℕ) : IsCompact (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Units.isEmbedding_val₀.isCompact_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [val_image_unitFiltrationUnits_zero]
    have : {y : K | valuation K y = 1} =
        {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
      constructor
      · intro h; exact ⟨h.le, h.ge⟩
      · intro h; exact le_antisymm h.1 h.2
    rw [this]
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff isOpen_setOf_valuation_lt
  · rw [val_image_unitFiltrationUnits hn hϖ]
    have : {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} =
        (Homeomorph.subRight (1 : K)) ⁻¹' {y : K | valuation K y ≤ valuation K (ϖ : K) ^ n} := by
      ext y; rfl
    rw [this, Homeomorph.isCompact_preimage]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K _
end GroundTheory.LocalField
