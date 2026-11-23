-- Prove2me | solution 1 for GlobalTheory.succMin_mono_of_isZLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:43.055295+00:00
-- url     : https://prove2.me/submissions/859ed2dd-1a51-4f3c-8837-af3c6fa0739d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_finrank_span_of_isZLattice
import Theorems.Thm_GlobalTheory_succMin_mono

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
theorem _root_.solution [DiscreteTopology L] [IsZLattice ℝ L] (hij : i ≤ j)
    (hj : j ≤ finrank ℝ E) : succMin L i ≤ succMin L j :=
  succMin_mono hij (by rwa [finrank_span_of_isZLattice])
end GlobalTheory
