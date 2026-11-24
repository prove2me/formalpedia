-- Prove2me | solution 1 for GlobalTheory.IsSiegel.natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:45.772648+00:00
-- url     : https://prove2.me/submissions/c9e7b6e6-32f4-4137-8527-d7137a036f30

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_smul

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
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℕ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by
  simpa using h.smul (q := q) (by exact_mod_cast hq)
end IsSiegel
end GlobalTheory
