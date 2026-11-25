-- Prove2me | solution 1 for GlobalTheory.Hk.RayCount.lamIdeal_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:46.707907+00:00
-- url     : https://prove2.me/submissions/ccba6d8f-5a18-4a82-be57-cffc2644442d

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
theorem _root_.solution (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h0 : P ≠ ⊥) (k : ℕ) (hk : 1 ≤ k) :
    lamIdeal (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [lamIdeal, if_pos ⟨P, k, hP, h0, hk, rfl⟩, Ideal.radical_pow _ (by omega), hP.radical]
end GlobalTheory.Hk.RayCount
