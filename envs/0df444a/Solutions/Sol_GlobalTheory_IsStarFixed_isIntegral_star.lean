-- Prove2me | solution 1 for GlobalTheory.IsStarFixed.isIntegral_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:57.179288+00:00
-- url     : https://prove2.me/submissions/2685ea06-1d46-45bf-9f42-aeac3a3ed52a

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
namespace GlobalTheory
namespace IsStarFixed
theorem _root_.solution {F E : Type*} [CommRing F] [CommRing E] [StarRing E]
    [Algebra F E] [IsStarFixed F E] {x : E} (hx : IsIntegral F x) : IsIntegral F (star x) :=
  hx.map (starAlgEquiv F E)
end IsStarFixed
end GlobalTheory
