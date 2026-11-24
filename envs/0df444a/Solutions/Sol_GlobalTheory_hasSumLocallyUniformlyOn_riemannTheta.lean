-- Prove2me | solution 1 for GlobalTheory.hasSumLocallyUniformlyOn_riemannTheta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:31.234524+00:00
-- url     : https://prove2.me/submissions/015b8045-ec15-49c8-857c-b6ae9b9b1f3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eventually_norm_riemannThetaTerm_le

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
    HasSumLocallyUniformlyOn
      (fun n (p : (ι → ℂ) × Matrix ι ι ℂ) => riemannThetaTerm a b p.2 p.1 n)
      (fun p => riemannTheta a b p.2 p.1) (Set.univ ×ˢ ReciprocityTheory.PTheta.SiegelH ι) := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun p hp => ?_
  obtain ⟨c, hc, S, hS⟩ := IsSiegel.exists_eventually_norm_riemannThetaTerm_le hp.2 a b p.1
  refine ⟨_, mem_nhdsWithin_of_mem_nhds hS, ?_⟩
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  exact tendstoUniformlyOn_tsum (summable_riemannThetaBound a hc S) fun n q hq => hq n
end GlobalTheory
