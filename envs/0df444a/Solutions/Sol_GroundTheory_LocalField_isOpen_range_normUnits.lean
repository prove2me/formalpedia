-- Prove2me | solution 1 for GroundTheory.LocalField.isOpen_range_normUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:33.41881+00:00
-- url     : https://prove2.me/submissions/d631f149-1ebf-4e40-a5ee-073d169b8ed7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltrationUnits_le_range_normUnits
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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
theorem _root_.solution : IsOpen ((normUnits K L).range : Set Kˣ) := by
  obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le_range_normUnits K L
  exact Subgroup.isOpen_mono hn (isOpen_unitFiltrationUnits n)
end GroundTheory.LocalField
