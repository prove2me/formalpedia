-- Prove2me | solution 1 for GlobalTheory.CMTensor.algebraMap_right_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:10.98931+00:00
-- url     : https://prove2.me/submissions/62475cd7-92de-469f-80f7-cf3935077c30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_StarTensor_algebraMap_right_injective

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
theorem _root_.solution : Function.Injective (algebraMap A (CMTensor E A)) :=
  StarTensor.algebraMap_right_injective (RingHom.injective _)
end GlobalTheory.CMTensor
