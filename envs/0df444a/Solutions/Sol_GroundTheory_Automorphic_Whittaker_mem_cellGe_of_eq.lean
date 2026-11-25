-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_cellGe_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:54.322935+00:00
-- url     : https://prove2.me/submissions/89b43947-dc92-4924-8a13-b802e0c81468

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_iff_llRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g h : GL (Fin n) F} (e : bruhatCell h = bruhatCell g) : h ∈ cellGe g :=
  fun i j => (bruhatCell_eq_iff_llRank.1 e i j).ge
end GroundTheory.Automorphic.Whittaker
