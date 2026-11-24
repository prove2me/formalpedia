-- Prove2me | solution 1 for GlobalTheory.LinearMapDifferenceFormula.map_sub_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:01.920214+00:00
-- url     : https://prove2.me/submissions/06e7a56a-e077-414a-bb83-ca114ed1a050

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapSubApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LinearMapDifferenceFormula
open AdicCompletion
namespace GlobalTheory.LinearMapDifferenceFormula
theorem _root_.solution {A : Type} [CommRing A] (J : Ideal A) {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h k : M →ₗ[A] P) (y : AdicCompletion J M) :
    AdicCompletion.map J (h - k) y = AdicCompletion.map J h y - AdicCompletion.map J k y := by
  induction y using AdicCompletion.induction_on with
  | h a =>
    ext n
    simp
end GlobalTheory.LinearMapDifferenceFormula
