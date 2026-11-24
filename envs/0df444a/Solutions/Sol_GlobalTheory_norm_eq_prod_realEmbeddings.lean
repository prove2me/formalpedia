-- Prove2me | solution 1 for GlobalTheory.norm_eq_prod_realEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:03.672224+00:00
-- url     : https://prove2.me/submissions/0afbd2c0-a122-49d8-9ffc-f395cba921a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_norm_eq_prod_complexEmbeddings
import Theorems.Thm_GlobalTheory_bijective_ofRealHom_comp

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
theorem _root_.solution (x : F) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, norm_eq_prod_complexEmbeddings, Complex.ofReal_prod]
  exact ((bijective_ofRealHom_comp F).prod_comp (fun φ => φ x)).symm
end GlobalTheory
