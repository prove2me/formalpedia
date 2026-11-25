-- Prove2me | solution 1 for GlobalTheory.Hk.RayCount.aRay_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:33.503614+00:00
-- url     : https://prove2.me/submissions/404cecc7-b0b1-44a2-ad95-f65b439694b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow

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
theorem _root_.solution (g : D.G) (n : ℕ) : aRay D g n = ((idealsIn_finite D g n).toFinset.card : ℝ) := by
  rw [aRay, Set.ncard_eq_toFinset_card _ (idealsIn_finite D g n)]
end GlobalTheory.Hk.RayCount
