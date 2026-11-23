-- Prove2me | solution 1 for GroundTheory.LocalField.one_le_absRamificationIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:23.419804+00:00
-- url     : https://prove2.me/submissions/0991268a-7e0d-4252-afb4-7e875e67eb9b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_natCast_prime

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
include p
namespace GroundTheory.LocalField
theorem _root_.solution : 1 ≤ absRamificationIndex K := by
  have h := normalizedValuation_natCast_prime (K := K) p
  have hlt : normalizedValuation K (p : K) < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact CharZero.valuation_p_lt_one K p
  rw [h, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega
end GroundTheory.LocalField
