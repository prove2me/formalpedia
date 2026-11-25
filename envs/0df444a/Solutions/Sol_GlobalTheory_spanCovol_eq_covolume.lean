-- Prove2me | solution 1 for GlobalTheory.spanCovol_eq_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:55.531351+00:00
-- url     : https://prove2.me/submissions/6b641201-c7be-4911-af12-bfc26b2c3bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_spanCovol_eq_sqrt_det_gram
import Theorems.Thm_GlobalTheory_covolume_eq_sqrt_det_gram


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
    [DiscreteTopology L] [IsZLattice ℝ L] : spanCovol L = ZLattice.covolume L := by
  rw [spanCovol_eq_sqrt_det_gram (finBasis ℤ L), covolume_eq_sqrt_det_gram L (finBasis ℤ L)]
end GlobalTheory
