-- Prove2me | solution 1 for GlobalTheory.entire_apply_eq_of_isZLattice_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:10.125463+00:00
-- url     : https://prove2.me/submissions/9121eecb-17f4-48a9-afbc-1846d60385b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hper : ∀ x, ∀ g ∈ L, F (x + g) = F x) (z w : E) : F z = F w :=
  hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L F hF.continuous hper).isBounded z w
end GlobalTheory
