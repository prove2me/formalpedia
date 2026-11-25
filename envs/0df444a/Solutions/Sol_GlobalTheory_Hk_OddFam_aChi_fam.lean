-- Prove2me | solution 1 for GlobalTheory.Hk.OddFam.aChi_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:46:29.208954+00:00
-- url     : https://prove2.me/submissions/8e9546c0-bdcd-47f6-8cbf-a8ed10a122a6

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
open GlobalTheory.Hk.OddFam
namespace GlobalTheory.Hk.OddFam
theorem _root_.solution (n : ℕ) : fam.aChi 1 n = if Odd n then 1 else 0 := by
  have : ∑ g : ZMod 1, (1 : AddChar (ZMod 1) ℂ) g * (ao n : ℂ) = if Odd n then 1 else 0 := by
    unfold ao; split_ifs <;> simp
  exact this
end GlobalTheory.Hk.OddFam
