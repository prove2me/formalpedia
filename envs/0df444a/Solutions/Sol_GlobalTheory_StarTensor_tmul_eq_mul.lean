-- Prove2me | solution 1 for GlobalTheory.StarTensor.tmul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:44.853594+00:00
-- url     : https://prove2.me/submissions/c95790d1-faea-444d-9ee3-5deb09bdac20

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
theorem _root_.solution (e : E) (a : A) :
    tmul F e a = algebraMap E (StarTensor F E A) e * algebraMap A (StarTensor F E A) a := by
  simp [algebraMap_left, algebraMap_right]
end GlobalTheory.StarTensor
