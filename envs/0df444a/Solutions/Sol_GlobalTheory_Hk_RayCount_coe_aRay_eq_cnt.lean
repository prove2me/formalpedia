-- Prove2me | solution 1 for GlobalTheory.Hk.RayCount.coe_aRay_eq_cnt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:37.378841+00:00
-- url     : https://prove2.me/submissions/1a2c8ec7-9605-48b9-a576-fd4eaa49431b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Theorems.Thm_GlobalTheory_Mem_RayData_cnt_of_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Hk
attribute [instance] LFam.ag LFam.ft
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : GlobalTheory.Mem.RayData K M)
open GlobalTheory.Hk.RayCount
namespace GlobalTheory.Hk.RayCount
theorem _root_.solution (g : D.G) {n : ℕ} (hn : n ≠ 0) : (aRay D g n : ℂ) = D.cnt g n := by
  rw [D.cnt_of_ne_zero g hn, aRay, ← Nat.card_coe_set_eq]
  norm_cast
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I => by simp only [idealsIn, Set.mem_setOf_eq]; tauto)
end GlobalTheory.Hk.RayCount
