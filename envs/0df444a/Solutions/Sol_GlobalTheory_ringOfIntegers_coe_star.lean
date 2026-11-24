-- Prove2me | solution 1 for GlobalTheory.ringOfIntegers_coe_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:10.807221+00:00
-- url     : https://prove2.me/submissions/cc334f9e-3028-4f90-aa41-e37baa1bc723

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
    algebraMap (𝓞 E) E (star x) = star (algebraMap (𝓞 E) E x) := rfl
end GlobalTheory
