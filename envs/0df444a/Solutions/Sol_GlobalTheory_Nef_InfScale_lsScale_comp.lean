-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.lsScale_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:04:06.795682+00:00
-- url     : https://prove2.me/submissions/31581c9c-055f-41b8-8d4b-dbe811d55171

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
theorem _root_.solution (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c) :=
  IsLocalization.lift_comp _
end GlobalTheory.Nef.InfScale
