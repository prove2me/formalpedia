-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.ratInv_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:04:07.986121+00:00
-- url     : https://prove2.me/submissions/f09352e4-8307-4c72-a2ac-1afa94310d07

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
theorem _root_.solution (p : F[X]) :
    ratInv (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p :=
  IsLocalization.lift_eq _ _
end GlobalTheory.Nef.InfScale
