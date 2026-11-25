-- Prove2me | solution 1 for GroundTheory.LocalField.sub_one_mul_padicValNat_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:29.467355+00:00
-- url     : https://prove2.me/submissions/4d69dd28-3004-49fb-9542-eec07cbbdb73

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
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n < n := by
  have h : padicValNat p n ≤ padicValNat p n.factorial := by
    rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
    exact pow_padicValNat_dvd.trans (Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl)
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h)
    (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
end GroundTheory.LocalField
