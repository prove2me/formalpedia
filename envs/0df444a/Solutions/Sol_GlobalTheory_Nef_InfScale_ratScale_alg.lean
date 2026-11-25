-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.ratScale_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:56.7408+00:00
-- url     : https://prove2.me/submissions/81857370-13f5-4334-9de9-e3e659244578

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.InfScale
theorem _root_.solution (c : F) (hc : c ≠ 0) (p : F[X]) :
    ratScale c hc (algebraMap F[X] (RatFunc F) p) = algebraMap F[X] (RatFunc F) (polyScale c p) :=
  IsLocalization.lift_eq _ _
end GlobalTheory.Nef.InfScale
