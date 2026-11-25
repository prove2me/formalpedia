-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.not_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:06:54.505776+00:00
-- url     : https://prove2.me/submissions/26659e31-c52b-492f-932b-9d094bd929f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution : ¬ NormOne 7 2 2 := by
  rintro ⟨A, B, h1, ⟨b, rfl⟩, -⟩
  push_cast at h1
  have h2 : A ≤ 2 := by nlinarith [sq_nonneg b]
  have h3 : -2 ≤ A := by nlinarith [sq_nonneg b]
  have h4 : b ≤ 0 := by nlinarith [sq_nonneg A]
  have h5 : 0 ≤ b := by nlinarith [sq_nonneg A]
  interval_cases A <;> interval_cases b <;> norm_num at h1
end GlobalTheory.Mem.An.Model
