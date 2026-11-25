-- Prove2me | solution 1 for GlobalTheory.succMin_pos_of_isZLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:36.735467+00:00
-- url     : https://prove2.me/submissions/47f24698-a03b-4a3c-ac07-cf01cebedf76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_finrank_span_of_isZLattice
import Theorems.Thm_GlobalTheory_succMin_pos

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
theorem _root_.solution [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]
    (h1 : 1 ≤ i) (hi : i ≤ finrank ℝ E) : 0 < succMin L i :=
  succMin_pos h1 (by rwa [finrank_span_of_isZLattice])
end GlobalTheory
