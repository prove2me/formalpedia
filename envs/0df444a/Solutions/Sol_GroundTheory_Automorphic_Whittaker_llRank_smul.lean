-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.llRank_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:23.474251+00:00
-- url     : https://prove2.me/submissions/ce1ed141-af6f-4434-aeb1-af92970817ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_unipotent_le_borel
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_mul_mul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_unipotent_le_borel


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
theorem _root_.solution (k : NN F n) (x : GL (Fin n) F) (i j : Fin n) :
    llRank i j (k • x) = llRank i j x :=
  llRank_mul_mul (unipotent_le_borel k.1.2)
    (unipotent_le_borel ((Iwasawa.unipotent F n).inv_mem k.2.2)) i j x
end GroundTheory.Automorphic.Whittaker
