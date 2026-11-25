-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.univ_conj_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:39.6272+00:00
-- url     : https://prove2.me/submissions/4047cbaa-729e-49e9-b825-9eed1a39305b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan

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
omit [TopologicalSpace F] [IsTopologicalRing F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ (univ : Set (GL (Fin n) F)),
    h • x ∈ (univ : Set (GL (Fin n) F)) := fun _ _ _ => mem_univ _
end GroundTheory.Automorphic.ContragredientTranspose
