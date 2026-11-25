-- Prove2me | solution 1 for GroundTheory.LocalField.exists_range_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:38.371495+00:00
-- url     : https://prove2.me/submissions/e2ca5813-8a62-4e65-b691-c2b856a53012

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe

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
theorem _root_.solution {H : Subgroup Kˣ} [H.FiniteIndex] :
    ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H := by
  refine ⟨H.index, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact H.pow_index_mem x
end GroundTheory.LocalField
