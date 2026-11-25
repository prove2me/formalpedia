-- Prove2me | solution 1 for GlobalTheory.exists_ideal_in_class_of_norm_le_sqrt_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:36.152064+00:00
-- url     : https://prove2.me/submissions/458821a8-50cd-4d9a-9d9c-a775e1725448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_minkowski_const_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ √|(discr K : ℝ)| := by
  obtain ⟨I, hI, hN⟩ := exists_ideal_in_class_of_norm_le C
  refine ⟨I, hI, hN.trans ?_⟩
  rw [← mul_assoc]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (minkowski_const_le_one K)
end GlobalTheory
