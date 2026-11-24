-- Prove2me | solution 1 for GlobalTheory.IsSiegel.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:46.933341+00:00
-- url     : https://prove2.me/submissions/f65042a2-10c2-4b59-a491-e9acd2f90b19

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
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℝ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by
  refine ⟨h.isSymm.smul _, ?_⟩
  convert h.posDef.smul hq using 1
  ext i j
  simp
end IsSiegel
end GlobalTheory
