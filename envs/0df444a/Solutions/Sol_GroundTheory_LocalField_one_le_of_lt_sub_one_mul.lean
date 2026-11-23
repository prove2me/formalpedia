-- Prove2me | solution 1 for GroundTheory.LocalField.one_le_of_lt_sub_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:15.260793+00:00
-- url     : https://prove2.me/submissions/2543eaf9-555b-483d-9ed5-7d03de0bd2da

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_one_le_absRamificationIndex

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
namespace GroundTheory.LocalField
theorem _root_.solution {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    1 ≤ a := by
  have he := one_le_absRamificationIndex (K := K) p
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  by_contra h
  push Not at h
  nlinarith
end GroundTheory.LocalField
