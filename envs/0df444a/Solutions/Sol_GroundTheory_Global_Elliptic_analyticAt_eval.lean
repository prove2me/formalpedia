-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:20.226844+00:00
-- url     : https://prove2.me/submissions/ec4f6a70-2129-4e35-84e8-64ccd982f5ad

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
theorem _root_.solution {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (P : ℂ[X]) :
    AnalyticAt ℂ (fun z ↦ P.eval (g z)) x := by
  simpa using hg.aeval_polynomial P
end GroundTheory.Global.Elliptic
