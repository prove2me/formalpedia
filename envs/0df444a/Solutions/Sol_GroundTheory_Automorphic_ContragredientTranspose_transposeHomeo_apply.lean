-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:40:24.984826+00:00
-- url     : https://prove2.me/submissions/f4af44e4-39d1-4cb5-9105-ba23a3a4ec63

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
variable {F : Type*} [Field F] {n : ℕ}
variable [TopologicalSpace F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (g : GL (Fin n) F) : transposeHomeo g = transposeGL g := rfl
end GroundTheory.Automorphic.ContragredientTranspose
