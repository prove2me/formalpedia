-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AdicCompletion.extendRingHom_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:53.405384+00:00
-- url     : https://prove2.me/submissions/3cdb0a69-fe08-4ff4-937b-08a21c3712c1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Theorems.Thm_GroundTheory_PAdicHodge_AdicCompletion_mk_extendRingHom

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
    (f : A →+* B) (hf : J ≤ I.comap f) (x : A) :
    AdicCompletion.extendRingHom J I f hf (AdicCompletion.of J A x) = f x := by
  have h := IsHausdorff.funext' I
    (f := fun y : A => AdicCompletion.extendRingHom J I f hf (AdicCompletion.of J A y)) (g := f)
    (fun n y => by
      rw [AdicCompletion.mk_extendRingHom, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk])
  exact congrFun h x
end AdicCompletion
end GroundTheory.PAdicHodge
