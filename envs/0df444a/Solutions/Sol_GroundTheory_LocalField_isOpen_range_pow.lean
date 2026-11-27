-- Prove2me | solution 1 for GroundTheory.LocalField.isOpen_range_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:56.832058+00:00
-- url     : https://prove2.me/submissions/881df5ac-abc8-400e-9dc8-e3576f15617e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltration_le_range_pow
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
theorem _root_.solution {m : ℕ} (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom m : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  refine Subgroup.isOpen_mono ?_ (isOpen_unitFiltrationUnits N)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := hN hu
  exact ⟨unitsIncl K x, by simp⟩
end GroundTheory.LocalField
