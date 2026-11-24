-- Prove2me | solution 1 for GlobalTheory.riemannThetaTerm_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:43.008537+00:00
-- url     : https://prove2.me/submissions/e7f3017d-9e00-43ad-af8d-e04cf168311c

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
namespace GlobalTheory
theorem _root_.solution (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm 0 0 Ω v n =
      cexp (2 * π * I * (((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))) / 2 +
        (fun i => (n i : ℂ)) ⬝ᵥ v)) := by
  simp [riemannThetaTerm_def]
end GlobalTheory
