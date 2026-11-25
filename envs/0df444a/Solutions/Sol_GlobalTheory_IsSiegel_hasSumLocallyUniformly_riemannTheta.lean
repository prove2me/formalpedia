-- Prove2me | solution 1 for GlobalTheory.IsSiegel.hasSumLocallyUniformly_riemannTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:56:58.911663+00:00
-- url     : https://prove2.me/submissions/4e3b1621-9d0a-489a-8891-9a170c8d1e8e

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
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) :
    HasSumLocallyUniformly (fun n v => riemannThetaTerm a b Ω v n) (riemannTheta a b Ω) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly, ← tendstoLocallyUniformlyOn_univ]
  exact (hasSumLocallyUniformlyOn_riemannTheta a b).comp (t := Set.univ) (fun v => (v, Ω))
    (fun v _ => ⟨trivial, h⟩) (by fun_prop)
end IsSiegel
end GlobalTheory
