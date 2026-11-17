-- Prove2me | solution 1 for N25.jqTwentyFive_mem_xH25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:11.82051+00:00
-- url     : https://prove2.me/submissions/c409561e-b7aa-4fd3-b85d-029f8d5c28d1

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0

set_option autoImplicit false

namespace N25

/-- The dilated j-series is in the literal level-25 carrier over every field. -/
theorem _root_.solution (K : Type*) [Field K] :
    ModularCurve.jqNModC K 25 ∈ ModularCurve.xHFunctionFieldC K 25 N25.H25 := by
  apply ModularCurve.x0_le_xHFunctionFieldC K 25 N25.H25
  apply ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 K 25
  exact ModularCurve.jqModCd_mem_full K 25 (dvd_refl 25)

end N25
