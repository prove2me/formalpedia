-- Prove2me | solution 2 for GlobalTheory.mul_star_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:06.364082+00:00
-- url     : https://prove2.me/submissions/c228169a-2984-4d94-a8d1-169cc44c009a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_star_eq_self_iff_mem

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
theorem _root_.solution (x : E) : x * star x ∈ maximalRealSubfield E :=
  (star_eq_self_iff_mem _).1 (by rw [star_mul, star_star])
end GlobalTheory
