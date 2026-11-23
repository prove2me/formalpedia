-- Prove2me | solution 1 for GlobalTheory.finrank_span_of_isZLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:41.648928+00:00
-- url     : https://prove2.me/submissions/b668be1e-681f-49b9-b1a9-a9263a51506d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    finrank ℝ (span ℝ (L : Set E)) = finrank ℝ E := by
  rw [IsZLattice.span_top, finrank_top]
end GlobalTheory
