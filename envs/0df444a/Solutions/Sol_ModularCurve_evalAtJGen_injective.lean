-- Prove2me | solution 1 for ModularCurve.evalAtJGen_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f2251c8f-27a4-5ac1-a883-ac8c888064c6

import Theorems.Thm_ModularCurve_PhiGen_evalAtJ_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_evalAtJGen_injective

open ModularCurve IntermediateField

theorem solution :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := by
  intro a b hab
  apply ModularCurve.PhiGen.evalAtJ_injective
  rw [← ModularCurve.algebraMap_comp_evalAtJGen, RingHom.comp_apply, RingHom.comp_apply, hab]

end S_ModularCurve_evalAtJGen_injective
end P2MW
export P2MW.S_ModularCurve_evalAtJGen_injective (solution)
