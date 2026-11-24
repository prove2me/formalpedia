-- Prove2me | solution 1 for GlobalTheory.IsStarFixed.star_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:19.106801+00:00
-- url     : https://prove2.me/submissions/ee707640-9be0-4779-bb00-27e3d0f93114

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
variable (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E]
variable [IsStarFixed F E]
variable {F E}
namespace GlobalTheory
namespace IsStarFixed
theorem _root_.solution (a : F) (x : E) : star (a • x) = a • star x :=
  map_smul (starAlgEquiv F E) a x
end IsStarFixed
end GlobalTheory
