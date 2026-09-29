-- Prove2me | solution 1 for ModularCurve.mapDomain_heckeDivBar_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/cd49c826-4738-5f01-adf1-50739ba57231

import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mapDomain_heckeDivBar_single

open AlgebraicCurve ModularCurve

theorem solution {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] {k F' : Type*} [Field k] [Field F'] [Algebra k F'] (sp : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k F') (v : Place L (laurentBaseChange L (modularFunctionFieldFull N))) (n : ℤ) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v n)) = ∑ W ∈ Place.fiberAlong (heckeBetaBar L N ℓ) hβ v, Finsupp.single (sp (W.restrictAlong (heckeAlphaBar L N ℓ) hα)) (n * (W.ramificationIndexAlong (heckeBetaBar L N ℓ) : ℤ) * (W.inertiaDegAlong (heckeAlphaBar L N ℓ) hα : ℤ)) := by
  rw [heckeDivBar, Divisor.correspondence_single, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]

end S_ModularCurve_mapDomain_heckeDivBar_single
end P2MW
export P2MW.S_ModularCurve_mapDomain_heckeDivBar_single (solution)
