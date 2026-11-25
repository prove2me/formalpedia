-- Prove2me | solution 1 for GlobalTheory.StarTensor.lift_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:12:33.880403+00:00
-- url     : https://prove2.me/submissions/7524a09e-fd9e-450f-9021-479afbd7e038

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
variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]
variable {B : Type*} [CommRing B] [Algebra F B]
namespace GlobalTheory.StarTensor
theorem _root_.solution {D : Type*} [CommRing D] [StarRing D] (f : E →+* D) (g : A →+* D) (hfg)
    (hf : ∀ e, f (star e) = star (f e)) (hg : ∀ a, star (g a) = g a)
    (x : StarTensor F E A) : lift f g hfg (star x) = star (lift f g hfg x) :=
  x.induction_on (by simp) (fun _ _ => by simp [hf, hg]) (fun x y hx hy => by simp [hx, hy])
end GlobalTheory.StarTensor
