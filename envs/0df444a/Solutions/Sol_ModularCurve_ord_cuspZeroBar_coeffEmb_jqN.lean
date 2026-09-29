-- Prove2me | solution 1 for ModularCurve.ord_cuspZeroBar_coeffEmb_jqN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1b3c39e8-c629-5465-b36d-e166f1842a84

import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) :
    (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ = -1 := by
  have e := ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand N h 1 N (one_mul N)
  rw [Nat.cast_one] at e
  exact e

end S_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN
end P2MW
export P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN (solution)
