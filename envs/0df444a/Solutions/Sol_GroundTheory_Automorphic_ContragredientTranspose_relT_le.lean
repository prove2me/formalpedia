-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.relT_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:31.506808+00:00
-- url     : https://prove2.me/submissions/1451bfa4-ec47-49d9-9d44-a9da168cb6e1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_tauSpan_le
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relSpan_le_supportedIn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {U : Set (GL (Fin n) F)} (hUinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U, h • x ∈ U)
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) : relT U ≤ supportedIn U :=
  sup_le (relSpan_le_supportedIn _ hUinv) (tauSpan_le hUτ)
end GroundTheory.Automorphic.ContragredientTranspose
