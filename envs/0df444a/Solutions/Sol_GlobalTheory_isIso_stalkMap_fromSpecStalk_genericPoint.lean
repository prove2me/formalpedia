-- Prove2me | solution 1 for GlobalTheory.isIso_stalkMap_fromSpecStalk_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:43.635101+00:00
-- url     : https://prove2.me/submissions/4a76967a-8f34-4a49-8148-a328fd4c0b63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {U T Z Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (U : Scheme.{u}) [IsIntegral U] :
    IsIso ((U.fromSpecStalk (genericPoint U)).stalkMap (genericPoint _)) := by
  let _ : Field (U.presheaf.stalk (genericPoint U)) := inferInstanceAs (Field U.functionField)
  have hsub : ∀ p q : Spec (U.presheaf.stalk (genericPoint U)), p = q := by
    intro p q
    apply PrimeSpectrum.ext
    rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top,
      (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top]
  rw [hsub (genericPoint _) (IsLocalRing.closedPoint _)]
  have e : (U.fromSpecStalk (genericPoint U)).stalkMap (IsLocalRing.closedPoint _) =
      Scheme.stalkClosedPointTo (U.fromSpecStalk (genericPoint U)) ≫
        (stalkClosedPointIso _).inv := by
    simp [Scheme.stalkClosedPointTo]
  rw [e, Scheme.stalkClosedPointTo_fromSpecStalk]
  infer_instance
end GlobalTheory
