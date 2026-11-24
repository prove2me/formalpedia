-- Prove2me | solution 1 for GlobalTheory.isSiegel_I_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:32.545798+00:00
-- url     : https://prove2.me/submissions/a6dca6d3-6ee0-4508-a157-4754550a2d50

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_isSiegel_diagonal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] : IsSiegel (I • (1 : Matrix ι ι ℂ)) := by
  rw [smul_one_eq_diagonal, isSiegel_diagonal_iff]
  simp
end GlobalTheory
