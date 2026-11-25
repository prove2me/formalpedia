-- Prove2me | solution 1 for GlobalTheory.Hk.RayCount.lamIdeal_of_not_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:42.461058+00:00
-- url     : https://prove2.me/submissions/dd8e4a16-fc58-4acd-9d78-174eeedfdc5e

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
theorem _root_.solution {I : Ideal (𝓞 K)}
    (h : ¬ ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) : lamIdeal I = 0 := by
  rw [lamIdeal, if_neg h]
end GlobalTheory.Hk.RayCount
