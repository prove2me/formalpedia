-- Prove2me | solution 1 for GroundTheory.LocalField.normalizedValuation_natCast_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:21.594321+00:00
-- url     : https://prove2.me/submissions/fe40ed3a-a538-4e70-bcbd-8f18a60b195c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
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
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution :
    normalizedValuation K (p : K) = WithZero.exp (-(absRamificationIndex K : ℤ)) := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hr : ringChar 𝓀[K] = p := ringChar.eq 𝓀[K] p
  have hlt : normalizedValuation K (p : K) < 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_lt_iff, map_one]
    exact CharZero.valuation_p_lt_one K p
  rw [normalizedValuation_eq_exp_ord hp0] at hlt ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [absRamificationIndex, hr, Int.toNat_of_nonneg (by omega)]
end GroundTheory.LocalField
