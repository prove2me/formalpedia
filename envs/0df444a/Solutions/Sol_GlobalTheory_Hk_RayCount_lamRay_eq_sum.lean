-- Prove2me | solution 1 for GlobalTheory.Hk.RayCount.lamRay_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:02.459037+00:00
-- url     : https://prove2.me/submissions/8016f7c3-51c6-483f-80af-e960492e30d4

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
theorem _root_.solution (g : D.G) (n : ℕ) : lamRay D g n = ∑ I ∈ (idealsIn_finite D g n).toFinset, lamIdeal I :=
  finsum_mem_eq_finite_toFinset_sum _ (idealsIn_finite D g n)
end GlobalTheory.Hk.RayCount
