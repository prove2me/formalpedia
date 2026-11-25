-- Prove2me | solution 1 for GroundTheory.LocalField.mul_self_le_two_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:24.713029+00:00
-- url     : https://prove2.me/submissions/165cb15e-947f-4f8f-910f-f04525181b5c

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
namespace GroundTheory.LocalField
theorem _root_.solution (v : ℕ) : v * v ≤ 2 ^ (v + 1) := by
  induction v with
  | zero => norm_num
  | succ v ih =>
    rcases Nat.lt_or_ge v 3 with h | h
    · interval_cases v <;> norm_num
    · rw [pow_succ]; nlinarith
end GroundTheory.LocalField
