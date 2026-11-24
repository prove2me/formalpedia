-- Prove2me | solution 1 for GlobalTheory.StarTensor.ringHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:37.879132+00:00
-- url     : https://prove2.me/submissions/86786c83-82cf-414b-a403-d263531fe447

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_StarTensor_tmul_eq_mul

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
theorem _root_.solution {C : Type*} [Semiring C] {f g : StarTensor F E A →+* C}
    (hE : ∀ e, f (algebraMap E _ e) = g (algebraMap E _ e))
    (hA : ∀ a, f (algebraMap A _ a) = g (algebraMap A _ a)) : f = g :=
  RingHom.ext fun x => x.induction_on (by simp)
    (fun e a => by rw [tmul_eq_mul, map_mul, map_mul, hE, hA])
    (fun x y hx hy => by rw [map_add, map_add, hx, hy])
end GlobalTheory.StarTensor
