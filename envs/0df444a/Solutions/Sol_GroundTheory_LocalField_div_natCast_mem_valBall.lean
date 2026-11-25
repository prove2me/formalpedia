-- Prove2me | solution 1 for GroundTheory.LocalField.div_natCast_mem_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:00.117922+00:00
-- url     : https://prove2.me/submissions/9c5494e4-3a7f-4da6-b435-8563da448675

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_natCast

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
theorem _root_.solution {a : ℤ} {x : K} (hx : x ∈ valBall K a) {n : ℕ} (hn : n ≠ 0) :
    x / n ∈ valBall K (a - absRamificationIndex K * padicValNat p n) := by
  rw [mem_valBall, map_div₀, normalizedValuation_natCast p hn, div_eq_mul_inv,
    ← WithZero.exp_neg, neg_neg, neg_sub, sub_eq_add_neg, WithZero.exp_add, mul_comm]
  exact mul_le_mul_right hx _
end GroundTheory.LocalField
