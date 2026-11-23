-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.two_lt_ell
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:19.757799+00:00
-- url     : https://prove2.me/submissions/3482a9ea-d990-4bb4-8366-a0b648c20bc2

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
open GlobalTheory.Hk.LFam
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.LFam
theorem _root_.solution (t : ℝ) : 2 < 𝓕.ell t := by
  have hB := 𝓕.B_ge
  have ht := abs_nonneg t
  have h8 : (8 : ℝ) ≤ 𝓕.B * (|t| + 2) := by nlinarith
  have h2 := Real.log_two_gt_d9
  have e : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_le_log (by norm_num) h8
  unfold ell
  linarith
end GlobalTheory.Hk.LFam
