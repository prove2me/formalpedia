-- Prove2me | solution 1 for GlobalTheory.hasSum_theta_of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:39.368259+00:00
-- url     : https://prove2.me/submissions/1ffa4773-0f4a-4f35-8da9-1c072d86a05e

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_hasSum_riemannTheta

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
    HasSum (thetaTerm a b z τ) (theta a b z τ) :=
  IsSiegel.hasSum_riemannTheta h a b z
end GlobalTheory
