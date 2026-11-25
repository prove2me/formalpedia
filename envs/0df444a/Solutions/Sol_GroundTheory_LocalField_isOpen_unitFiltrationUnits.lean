-- Prove2me | solution 1 for GroundTheory.LocalField.isOpen_unitFiltrationUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:44.227474+00:00
-- url     : https://prove2.me/submissions/a7b46e1e-0951-4ea7-a719-e2d5f098217e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_zero_iff
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_iff
import Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_valuation_sub_le
import Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_valuation_eq_one
import Theorems.Thm_GroundTheory_LocalField_valuation_uniformizer_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℕ) : IsOpen (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (unitFiltrationUnits K 0 : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K y = 1} := by
      ext x; exact mem_unitFiltrationUnits_zero_iff
    rw [this]
    exact isOpen_setOf_valuation_eq_one.preimage Units.continuous_val
  · have : (unitFiltrationUnits K n : Set Kˣ) =
        (↑) ⁻¹' {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
      ext x; exact mem_unitFiltrationUnits_iff hn hϖ
    rw [this]
    exact (isOpen_setOf_valuation_sub_le
      (pow_ne_zero _ (valuation_uniformizer_ne_zero hϖ))).preimage Units.continuous_val
end GroundTheory.LocalField
