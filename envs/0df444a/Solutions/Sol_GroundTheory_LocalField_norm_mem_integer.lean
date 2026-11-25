-- Prove2me | solution 1 for GroundTheory.LocalField.norm_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:33.290801+00:00
-- url     : https://prove2.me/submissions/ebecebc9-dbc0-4751-940a-99e4a979aeca

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_coe_norm_integer

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
namespace GroundTheory.LocalField
theorem _root_.solution {x : L} (hx : x ∈ 𝒪[L]) : Algebra.norm K x ∈ 𝒪[K] := by
  have h := coe_norm_integer (K := K) (⟨x, hx⟩ : 𝒪[L])
  rw [← h]
  exact (Algebra.norm 𝒪[K] (⟨x, hx⟩ : 𝒪[L])).2
end GroundTheory.LocalField
