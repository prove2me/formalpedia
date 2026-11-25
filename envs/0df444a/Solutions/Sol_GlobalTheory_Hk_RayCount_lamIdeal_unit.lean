-- Prove2me | solution 1 for GlobalTheory.Hk.RayCount.lamIdeal_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:52:07.721832+00:00
-- url     : https://prove2.me/submissions/eaffc74a-b5ea-492e-9fd0-8758408d66f2

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
theorem _root_.solution : lamIdeal (⊤ : Ideal (𝓞 K)) = 0 := by
  unfold lamIdeal; split_ifs <;> simp
end GlobalTheory.Hk.RayCount
