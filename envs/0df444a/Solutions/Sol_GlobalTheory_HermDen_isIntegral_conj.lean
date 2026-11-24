-- Prove2me | solution 1 for GlobalTheory.HermDen.isIntegral_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:50.507917+00:00
-- url     : https://prove2.me/submissions/8c147bee-b342-4295-80b6-14eccb992e51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HermDen
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory.HermDen
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {x : E}
    (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
end GlobalTheory.HermDen
