-- Prove2me | solution 1 for GlobalTheory.Published.SuccMinTransference.of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:19.919509+00:00
-- url     : https://prove2.me/submissions/2b4107e2-a741-49a3-b38d-5ead6414ca4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_BesselIntegrals_ExistsLinearIndependentNormLe

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
open GlobalTheory GlobalTheory.Published
namespace GlobalTheory.Published
namespace SuccMinTransference
theorem _root_.solution
    (h : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (i : ℕ), 1 ≤ i →
      i ≤ finrank ℝ E →
      succMin L i * succMin (dualLattice L) (finrank ℝ E - i + 1) ≤ finrank ℝ E) :
    SuccMinTransference := by
  intro n L _ _ i h1 hi
  simpa using h _ L i h1 (by simpa using hi)
end SuccMinTransference
end GlobalTheory.Published
