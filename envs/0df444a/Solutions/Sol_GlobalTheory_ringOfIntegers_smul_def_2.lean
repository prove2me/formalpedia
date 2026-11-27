-- Prove2me | solution 2 for GlobalTheory.ringOfIntegers_smul_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:37.995395+00:00
-- url     : https://prove2.me/submissions/8787df4b-9c1a-4bb4-91e8-ee7d1397791a

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
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
variable {K V}
namespace GlobalTheory
theorem _root_.solution (a : 𝓞 K) (x : V) : a • x = (a : K) • x := rfl
end GlobalTheory
