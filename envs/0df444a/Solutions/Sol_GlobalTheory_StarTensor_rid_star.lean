-- Prove2me | solution 1 for GlobalTheory.StarTensor.rid_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:14:37.538994+00:00
-- url     : https://prove2.me/submissions/2c73a825-3181-4a05-811b-d5d64743b37c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_IsStarFixed_star_smul

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
variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]
variable {B : Type*} [CommRing B] [Algebra F B]
namespace GlobalTheory.StarTensor
theorem _root_.solution (x : StarTensor F E F) : rid F E (star x) = star (rid F E x) :=
  x.induction_on (by simp) (fun _ _ => by simp [IsStarFixed.star_smul])
    (fun x y hx hy => by simp [hx, hy])
end GlobalTheory.StarTensor
