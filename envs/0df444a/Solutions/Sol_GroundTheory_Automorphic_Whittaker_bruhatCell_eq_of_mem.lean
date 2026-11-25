-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bruhatCell_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:50.12869+00:00
-- url     : https://prove2.me/submissions/aeaa7d5b-c77e-4bda-9ae9-2028fd843a64

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
theorem _root_.solution {g h : GL (Fin n) F} (h₁ : h ∈ cellGe g) (h₂ : h ∈ cellLe g) :
    bruhatCell h = bruhatCell g :=
  bruhatCell_eq_iff_llRank.2 fun i j => le_antisymm (h₂ i j) (h₁ i j)
end GroundTheory.Automorphic.Whittaker
