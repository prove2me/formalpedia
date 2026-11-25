-- Prove2me | solution 1 for GlobalTheory.StarTensor.one_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:14:33.937615+00:00
-- url     : https://prove2.me/submissions/d9c4ba4c-40ce-4227-9e5b-cc1135b2c410

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
open GlobalTheory.StarTensor
variable (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
variable {F E A}
namespace GlobalTheory.StarTensor
theorem _root_.solution : (1 : StarTensor F E A) = tmul F 1 1 := rfl
end GlobalTheory.StarTensor
