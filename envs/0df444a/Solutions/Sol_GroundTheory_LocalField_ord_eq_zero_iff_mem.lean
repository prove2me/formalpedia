-- Prove2me | solution 1 for GroundTheory.LocalField.ord_eq_zero_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:57.488949+00:00
-- url     : https://prove2.me/submissions/e5813e63-b780-4647-951e-d6675e52ea8c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_zero_iff
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord


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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {x : Kˣ} : ord (x : K) = 0 ↔ x ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, ← map_one (valuation K), ← normalizedValuation_eq_iff,
    normalizedValuation_eq_exp_ord x.ne_zero, map_one, ← WithZero.exp_zero, WithZero.exp_inj,
    neg_eq_zero]
end GroundTheory.LocalField
