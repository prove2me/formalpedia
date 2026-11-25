-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AdicCompletion.mk_extendRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:06:30.171177+00:00
-- url     : https://prove2.me/submissions/794a229f-b4b3-4de2-9627-3326b1c93624

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.PAdicHodge
namespace AdicCompletion
theorem _root_.solution (J : Ideal A) (I : Ideal B) [IsAdicComplete I B]
    (f : A →+* B) (hf : J ≤ I.comap f) (n : ℕ) (x : AdicCompletion J A) :
    Ideal.Quotient.mk (I ^ n) (AdicCompletion.extendRingHom J I f hf x) =
      Ideal.quotientMap (I ^ n) f ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n))
        (AdicCompletion.evalₐ J n x) :=
  IsAdicComplete.mk_liftRingHom I _ _ n x
end AdicCompletion
end GroundTheory.PAdicHodge
