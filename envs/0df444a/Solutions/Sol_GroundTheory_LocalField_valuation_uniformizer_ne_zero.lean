-- Prove2me | solution 1 for GroundTheory.LocalField.valuation_uniformizer_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:17:34.431616+00:00
-- url     : https://prove2.me/submissions/dcc2bb27-ed8e-409f-9fb7-2931ac78e497

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
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hϖ.ne_zero
end GroundTheory.LocalField
