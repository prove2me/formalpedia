-- Prove2me | solution 2 for GlobalTheory.eq_zero_or_totallyPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:58.055408+00:00
-- url     : https://prove2.me/submissions/bb69b50d-a0f6-403b-a8f2-08f09766b85b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_eq_zero_of_embedding_eq_zero

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
theorem _root_.solution {a : F} (ha : ∀ σ : F →+* ℝ, 0 ≤ σ a) :
    a = 0 ∨ ∀ σ : F →+* ℝ, 0 < σ a := by
  by_cases h0 : a = 0
  · exact Or.inl h0
  · exact Or.inr fun σ => (ha σ).lt_of_ne' fun h => h0 (eq_zero_of_embedding_eq_zero σ h)
end GlobalTheory
