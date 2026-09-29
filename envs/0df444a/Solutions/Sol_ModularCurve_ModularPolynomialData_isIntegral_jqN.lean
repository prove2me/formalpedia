-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.isIntegral_jqN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/12b3ebdc-4713-5fec-84d4-fcc6fb481bd5

import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN

open ModularCurve IntermediateField

noncomputable section

theorem solution {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) :=by
  refine ⟨data.toAdjoin, data.toAdjoin_monic, ?_⟩
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

end

end S_ModularCurve_ModularPolynomialData_isIntegral_jqN
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN (solution)
