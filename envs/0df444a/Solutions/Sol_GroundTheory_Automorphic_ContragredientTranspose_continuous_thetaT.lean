-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.continuous_thetaT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:37.238867+00:00
-- url     : https://prove2.me/submissions/50828795-456b-48f1-948f-9db8d42ce098

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv


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
theorem _root_.solution [IsTopologicalRing F] : Continuous (thetaT : GL (Fin n) F → GL (Fin n) F) :=
  continuous_transposeGL.inv
end GroundTheory.Automorphic.ContragredientTranspose
