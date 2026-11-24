-- Prove2me | solution 1 for GlobalTheory.ne_zero_of_totallyPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:25.506832+00:00
-- url     : https://prove2.me/submissions/1c03c4db-7b93-4a6d-9dd4-509209a014ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_norm_pos_of_totallyPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory
theorem _root_.solution {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) : a ≠ 0 := by
  rintro rfl
  simpa using norm_pos_of_totallyPos ha
end GlobalTheory
