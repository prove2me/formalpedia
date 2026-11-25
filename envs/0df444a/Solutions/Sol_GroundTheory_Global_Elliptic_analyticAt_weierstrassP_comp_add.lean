-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_weierstrassP_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:03.680798+00:00
-- url     : https://prove2.me/submissions/843b34c1-4a72-49ae-a793-d38b1d2082a6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {x w : ℂ} (h : x + w ∉ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] (z + w)) x :=
  (L.analyticOnNhd_weierstrassP (x + w) h).comp (g := ℘[L]) (f := fun z ↦ z + w) (by fun_prop)
end GroundTheory.Global.Elliptic
