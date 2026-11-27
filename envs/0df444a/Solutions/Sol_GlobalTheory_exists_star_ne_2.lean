-- Prove2me | solution 2 for GlobalTheory.exists_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:41.565787+00:00
-- url     : https://prove2.me/submissions/0161237d-b4b3-4ad2-a114-ba85274e8434

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
variable (E)
namespace GlobalTheory
theorem _root_.solution : ∃ x : E, star x ≠ x := by
  by_contra! H
  exact IsCMField.complexConj_ne_one E (AlgEquiv.ext H)
end GlobalTheory
