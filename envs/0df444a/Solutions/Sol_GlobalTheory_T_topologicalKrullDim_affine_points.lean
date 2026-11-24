-- Prove2me | solution 1 for GlobalTheory.T.topologicalKrullDim_affine_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:25.860653+00:00
-- url     : https://prove2.me/submissions/0fb9a713-4b3e-4aa5-a7ff-be9f5d3b820b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePointsStatement
import Theorems.Thm_GlobalTheory_FlagPts_topologicalKrullDim_affPts_eq_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J], topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  first | exact @GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card | exact GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card | (intros; apply GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card <;> assumption)
end _root_.GlobalTheory.T
