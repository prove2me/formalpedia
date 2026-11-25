-- Prove2me | solution 1 for GlobalTheory.spanCovol_comap_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:17.852486+00:00
-- url     : https://prove2.me/submissions/df4d0f66-43b8-4b7d-a794-cb00fbe8f636

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_spanCovol_map_linearIsometry
import Theorems.Thm_GlobalTheory_fg_of_discrete

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
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] (S : Submodule ℝ E)
    (h : (L : Set E) ⊆ S) : spanCovol (ZLattice.comap ℝ L S.subtype) = spanCovol L := by
  rw [← spanCovol_map_linearIsometry (fg_of_discrete _) S.subtypeₗᵢ]
  congr 1
  exact map_comap_eq_self fun x hx => ⟨⟨x, h hx⟩, rfl⟩
end GlobalTheory
