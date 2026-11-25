-- Prove2me | solution 1 for GlobalTheory.StarTensor.map_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:12:38.23621+00:00
-- url     : https://prove2.me/submissions/60e86bc9-02c8-4fff-822d-3091ee10ee69

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
variable {B C : Type*} [CommRing B] [CommRing C] [Algebra F B] [Algebra F C]
namespace GlobalTheory.StarTensor
theorem _root_.solution (g : B →ₐ[F] C) (f : A →ₐ[F] B) :
    map E (g.comp f) = (map E g).comp (map E f) :=
  AlgHom.ext fun x => x.induction_on (by simp) (fun _ _ => rfl)
    (fun x y hx hy => by rw [map_add, map_add, hx, hy])
end GlobalTheory.StarTensor
