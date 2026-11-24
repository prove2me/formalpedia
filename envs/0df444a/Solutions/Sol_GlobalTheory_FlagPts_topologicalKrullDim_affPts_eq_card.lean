-- Prove2me | solution 1 for GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:11.645896+00:00
-- url     : https://prove2.me/submissions/62189d4a-d9ba-4e69-8fd8-74dda305ef14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
import Theorems.Thm_GlobalTheory_FlagPts_topologicalKrullDim_affPts_le
import Theorems.Thm_GlobalTheory_FlagPts_le_topologicalKrullDim_affPts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts
open MvPolynomial
variable {k : Type} [Field k] {J : Type}
namespace GlobalTheory.FlagPts
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J],
      topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  intro k _ _ J _
  haveI : Infinite k := inferInstance
  exact le_antisymm topologicalKrullDim_affPts_le le_topologicalKrullDim_affPts
end GlobalTheory.FlagPts
