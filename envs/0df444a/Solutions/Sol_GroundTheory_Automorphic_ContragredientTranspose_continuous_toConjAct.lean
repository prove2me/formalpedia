-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.continuous_toConjAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:49.427054+00:00
-- url     : https://prove2.me/submissions/8dc6a9ce-ff6d-4de4-9be3-cd3d69910459

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
variable {G : Type*} [Group G] [TopologicalSpace G]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution : Continuous (ConjAct.toConjAct : G → ConjAct G) := continuous_id
end GroundTheory.Automorphic.ContragredientTranspose
