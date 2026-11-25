-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticOnNhd_modularJC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:56:23.915151+00:00
-- url     : https://prove2.me/submissions/6b46edb6-d534-4fc7-a242-895fb7d84614

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
import Theorems.Thm_GroundTheory_Global_Elliptic_differentiableOn_modularJC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution : AnalyticOnNhd ℂ modularJC {z : ℂ | 0 < z.im} :=
  differentiableOn_modularJC.analyticOnNhd isOpen_upperHalfPlaneSet
end GroundTheory.Global.Elliptic
