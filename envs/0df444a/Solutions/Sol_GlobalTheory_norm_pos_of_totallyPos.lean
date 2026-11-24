-- Prove2me | solution 1 for GlobalTheory.norm_pos_of_totallyPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:44.285552+00:00
-- url     : https://prove2.me/submissions/1e22ecfe-ede1-4eaf-9d94-1d4e4a3232b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_norm_eq_prod_realEmbeddings

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
theorem _root_.solution {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) : 0 < Algebra.norm ℚ a := by
  have : (0 : ℝ) < ((Algebra.norm ℚ a : ℚ) : ℝ) := by
    rw [norm_eq_prod_realEmbeddings]
    exact Finset.prod_pos fun σ _ => ha σ
  exact_mod_cast this
end GlobalTheory
