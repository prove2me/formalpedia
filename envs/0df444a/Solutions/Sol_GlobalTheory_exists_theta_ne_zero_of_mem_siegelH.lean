-- Prove2me | solution 1 for GlobalTheory.exists_theta_ne_zero_of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:58.497023+00:00
-- url     : https://prove2.me/submissions/ad7bed41-a59f-409f-8d29-ed7dcfdfbde5

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
theorem _root_.solution {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι) (a b : ι → ℝ) :
    ∃ z, theta a b z τ ≠ 0 :=
  Function.ne_iff.mp (IsSiegel.riemannTheta_ne_zero h a b)
end GlobalTheory
