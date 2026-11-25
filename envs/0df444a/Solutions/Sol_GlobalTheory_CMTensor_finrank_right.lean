-- Prove2me | solution 1 for GlobalTheory.CMTensor.finrank_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:14.477022+00:00
-- url     : https://prove2.me/submissions/67c804b4-3b12-40fa-a844-d632efdc3834

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
attribute [simp] IsStarFixed.star_algebraMap
variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.CMTensor
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]
namespace GlobalTheory.CMTensor
theorem _root_.solution [StrongRankCondition A] : Module.finrank A (CMTensor E A) = 2 := by
  rw [(StarTensor.commRight _ E A).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
    Algebra.IsQuadraticExtension.finrank_eq_two]
end GlobalTheory.CMTensor
