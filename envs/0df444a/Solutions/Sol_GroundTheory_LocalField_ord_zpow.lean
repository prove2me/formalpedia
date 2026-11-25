-- Prove2me | solution 1 for GroundTheory.LocalField.ord_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:46:38.071593+00:00
-- url     : https://prove2.me/submissions/7f464fdb-2b92-4445-a1a8-d8f4484da042

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
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
theorem _root_.solution {x : K} (hx : x ≠ 0) (k : ℤ) : ord (x ^ k) = k * ord x := by
  have h1 := normalizedValuation_eq_exp_ord (zpow_ne_zero k hx)
  rw [map_zpow₀, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zsmul, WithZero.exp_inj,
    smul_eq_mul] at h1
  linear_combination h1
end GroundTheory.LocalField
