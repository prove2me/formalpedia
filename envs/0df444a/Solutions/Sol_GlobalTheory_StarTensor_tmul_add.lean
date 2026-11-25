-- Prove2me | solution 1 for GlobalTheory.StarTensor.tmul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:15.577603+00:00
-- url     : https://prove2.me/submissions/1495ef33-5c1d-4b55-9917-784bdad43c9f

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
theorem _root_.solution (e : E) (a a' : A) : tmul F e (a + a') = tmul F e a + tmul F e a' :=
  TensorProduct.tmul_add e a a'
end GlobalTheory.StarTensor
