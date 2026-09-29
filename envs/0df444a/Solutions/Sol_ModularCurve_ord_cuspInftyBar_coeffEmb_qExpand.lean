-- Prove2me | solution 1 for ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8513c9db-de1b-50b9-89f5-ee4c8350f3f0

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.Thm_ModularCurve_order_coeffEmb
import Theorems.Thm_ModularCurve_order_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := by
  rw [ModularCurve.ord_cuspInftyBar]
  change (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)).order = _
  rw [ModularCurve.order_coeffEmb, ModularCurve.order_qExpand, order_jq, mul_neg, mul_one]

end S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
end P2MW
export P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand (solution)
