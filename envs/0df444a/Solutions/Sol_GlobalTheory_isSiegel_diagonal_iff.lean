-- Prove2me | solution 1 for GlobalTheory.isSiegel_diagonal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:36.206111+00:00
-- url     : https://prove2.me/submissions/bd7c9f5e-7038-4d2f-8643-2d938c316777

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
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] {τ : ι → ℂ} :
    IsSiegel (diagonal τ) ↔ ∀ i, 0 < (τ i).im := by
  have : (diagonal τ).map Complex.im = diagonal fun i => (τ i).im := diagonal_map (by simp)
  refine ⟨fun h => ?_, fun h => ⟨isSymm_diagonal _, ?_⟩⟩
  · simpa [this] using h.posDef
  · simpa [this] using h
end GlobalTheory
