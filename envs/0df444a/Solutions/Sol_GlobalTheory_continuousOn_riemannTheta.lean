-- Prove2me | solution 1 for GlobalTheory.continuousOn_riemannTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:57.693841+00:00
-- url     : https://prove2.me/submissions/a037762c-833d-43cd-bc7c-ad34795f3d8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_hasSumLocallyUniformlyOn_riemannTheta
import Theorems.Thm_GlobalTheory_continuous_riemannThetaTerm

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
namespace GlobalTheory
theorem _root_.solution (a b : ι → ℝ) :
    ContinuousOn (fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannTheta a b p.2 p.1)
      (Set.univ ×ˢ ReciprocityTheory.PTheta.SiegelH ι) :=
  TendstoLocallyUniformlyOn.continuousOn (hasSumLocallyUniformlyOn_riemannTheta a b)
    (Frequently.of_forall fun s =>
      (continuous_finsetSum s fun n _ => continuous_riemannThetaTerm a b n).continuousOn)
end GlobalTheory
