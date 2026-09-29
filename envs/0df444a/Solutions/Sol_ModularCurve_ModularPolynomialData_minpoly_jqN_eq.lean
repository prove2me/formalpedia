-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.minpoly_jqN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/45248148-67d9-5883-8f16-10daf2d0d034

import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq

open ModularCurve IntermediateField

theorem solution {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hirr : ModularCurve.PhiIrreducible data) :
    minpoly (↥ℚ⟮ModularCurve.jq⟯) (ModularCurve.jqN N) = data.toAdjoin :=
  ModularCurve.minpoly_jqN_eq_toAdjoin data hirr

end S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq (solution)
