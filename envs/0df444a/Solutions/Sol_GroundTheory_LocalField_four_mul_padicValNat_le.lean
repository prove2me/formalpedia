-- Prove2me | solution 1 for GroundTheory.LocalField.four_mul_padicValNat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:47.705614+00:00
-- url     : https://prove2.me/submissions/a61c81d0-848b-43f8-890e-4cad7cb6f9b2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_mul_self_le_two_pow_succ

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
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (c : ℕ) {n : ℕ} (hn : n ≠ 0) :
    4 * c * padicValNat p n ≤ n + 32 * c ^ 2 := by
  set v := padicValNat p n
  have h1 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp.out.two_le v
  have h2 : p ^ v ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  have h3 := mul_self_le_two_pow_succ v
  rw [pow_succ] at h3
  rcases Nat.lt_or_ge v (8 * c) with h | h
  · nlinarith
  · nlinarith
end GroundTheory.LocalField
