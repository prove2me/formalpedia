-- Prove2me | solution 1 for ModularCurve.isPrincipal_of_degree_eq_zero_charLOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c652d9b4-be25-5917-9a17-ef38a2880daa

import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne
open AlgebraicCurve ModularCurve

theorem solution {k : Type*} [Field k] (D : Divisor k (modularFunctionFieldC k 1))
    (hD : Divisor.degree D = 0) : D.IsPrincipal :=
  Pic0.forall_isPrincipal_of_ringEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a)
    (fun E hE => RationalFunctionField.isPrincipal_of_degree_eq_zero E hE) D hD

end S_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne
end P2MW
export P2MW.S_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne (solution)
