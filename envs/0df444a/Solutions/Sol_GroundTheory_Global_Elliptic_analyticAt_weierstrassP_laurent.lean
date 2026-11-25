-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_weierstrassP_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:22.532281+00:00
-- url     : https://prove2.me/submissions/7f537938-5d49-4c99-a8d0-7650e9fe5c82

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution :
    AnalyticAt ℂ (fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1) 0 := by
  have := L.analyticAt_weierstrassPExcept 0
  fun_prop
end GroundTheory.Global.Elliptic
