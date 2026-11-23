-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.isEllipticFunction_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.169979+00:00
-- url     : https://prove2.me/submissions/5a6a42f8-94c0-4fa2-b87c-c28b40419b66

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_weierstrassP

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
theorem _root_.solution : IsEllipticFunction L ℘[L] :=
  ⟨L.meromorphic_weierstrassP, isPeriodic_weierstrassP⟩
end GroundTheory.Global.Elliptic
