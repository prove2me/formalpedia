-- Prove2me | solution 1 for GroundTheory.LocalField.normalizedValuation_natCast_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:18.176906+00:00
-- url     : https://prove2.me/submissions/2c3117cc-adad-48ca-a64a-7c70e8f33fec

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries

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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
omit hp [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {m : ℕ} (hm : ¬ p ∣ m) :
    normalizedValuation K (m : K) = 1 := by
  rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]
  have := (CharZero.valuation_intCast_eq_one_iff K p (m : ℤ)).mpr (by exact_mod_cast hm)
  exact_mod_cast this
end GroundTheory.LocalField
