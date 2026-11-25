-- Prove2me | solution 1 for GlobalTheory.spanCovol_eq_covolume_comap_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:41.897807+00:00
-- url     : https://prove2.me/submissions/a121c71a-735a-4889-88b1-61eb043b3d53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_spanCovol_eq_covolume
import Theorems.Thm_GlobalTheory_spanCovol_comap_subtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] :
    spanCovol L = ZLattice.covolume (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) := by
  rw [← spanCovol_eq_covolume, spanCovol_comap_subtype L _ subset_span]
end GlobalTheory
