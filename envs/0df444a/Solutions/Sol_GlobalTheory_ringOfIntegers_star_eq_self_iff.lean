-- Prove2me | solution 1 for GlobalTheory.ringOfIntegers_star_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:43.960262+00:00
-- url     : https://prove2.me/submissions/fc3741e6-3e89-4900-98e5-44422f88cea3

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
namespace GlobalTheory
theorem _root_.solution (x : 𝓞 E) :
    star x = x ↔ x ∈ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)).range :=
  IsCMField.ringOfIntegersComplexConj_eq_self_iff E x
end GlobalTheory
