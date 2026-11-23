-- Prove2me | solution 1 for GlobalTheory.analyticOnNhd_weierstrassZeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:07.254675+00:00
-- url     : https://prove2.me/submissions/f9c5afc4-73bb-421e-be62-229acd710d43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution :
    AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_weierstrassZeta L hz).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl
end GlobalTheory
