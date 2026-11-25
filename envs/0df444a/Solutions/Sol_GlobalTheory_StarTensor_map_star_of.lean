-- Prove2me | solution 1 for GlobalTheory.StarTensor.map_star_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:14:30.822834+00:00
-- url     : https://prove2.me/submissions/fad6b7cc-df09-4f59-9667-bc2f117620e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_StarTensor_ringHom_ext

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
namespace GlobalTheory.StarTensor
theorem _root_.solution {C : Type*} [CommRing C] [StarRing C] (φ : StarTensor F E A →+* C)
    (hE : ∀ e, φ (algebraMap E _ (star e)) = star (φ (algebraMap E _ e)))
    (hA : ∀ a, star (φ (algebraMap A _ a)) = φ (algebraMap A _ a)) (x : StarTensor F E A) :
    φ (star x) = star (φ x) :=
  DFunLike.congr_fun (ringHom_ext (f := φ.comp (starRingEnd _)) (g := (starRingEnd C).comp φ)
    hE (fun a => by simpa [starRingEnd_apply] using (hA a).symm)) x
end GlobalTheory.StarTensor
