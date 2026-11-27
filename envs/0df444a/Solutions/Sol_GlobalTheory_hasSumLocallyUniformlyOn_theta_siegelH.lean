-- Prove2me | solution 1 for GlobalTheory.hasSumLocallyUniformlyOn_theta_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:29.929525+00:00
-- url     : https://prove2.me/submissions/77dc2b87-2427-4409-9f03-f3a455ce814a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_hasSumLocallyUniformlyOn_riemannTheta

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
variable [Fintype ι] [Fintype κ]
open ReciprocityTheory.PTheta
namespace GlobalTheory
theorem _root_.solution (a b : ι → ℝ) :
    HasSumLocallyUniformlyOn (fun l (p : (ι → ℂ) × Matrix ι ι ℂ) => thetaTerm a b p.1 p.2 l)
      (fun p => theta a b p.1 p.2) (Set.univ ×ˢ SiegelH ι) :=
  hasSumLocallyUniformlyOn_riemannTheta a b
end GlobalTheory
