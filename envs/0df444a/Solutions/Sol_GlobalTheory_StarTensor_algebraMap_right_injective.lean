-- Prove2me | solution 1 for GlobalTheory.StarTensor.algebraMap_right_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:42.955925+00:00
-- url     : https://prove2.me/submissions/d0153d61-9a2d-446b-8f99-3ba193cf8dab

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
theorem _root_.solution [Module.Flat F A] (hE : Function.Injective (algebraMap F E)) :
    Function.Injective (algebraMap A (StarTensor F E A)) :=
  Algebra.TensorProduct.includeRight_injective hE
end GlobalTheory.StarTensor
