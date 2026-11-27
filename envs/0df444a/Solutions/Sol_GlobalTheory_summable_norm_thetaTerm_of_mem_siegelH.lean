-- Prove2me | solution 1 for GlobalTheory.summable_norm_thetaTerm_of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:42.864861+00:00
-- url     : https://prove2.me/submissions/8a5c1f42-93a3-4e3f-8d3d-37507b241643

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

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
theorem _root_.solution {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) :
    Summable fun l => ‖thetaTerm a b z τ l‖ :=
  IsSiegel.summable_norm_riemannThetaTerm h a b z
end GlobalTheory
