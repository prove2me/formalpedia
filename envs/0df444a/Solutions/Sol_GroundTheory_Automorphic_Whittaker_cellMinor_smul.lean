-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.cellMinor_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:07:06.186232+00:00
-- url     : https://prove2.me/submissions/ec20e25b-69b9-4d9e-8b24-a864ed49d870

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_mul_mul


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
theorem _root_.solution {x : GL (Fin n) F} {w : Equiv.Perm (Fin n)} (hx : bruhatCell x = w)
    (k : NN F n) : cellMinor w (k • x) = cellMinor w x :=
  cellMinor_mul_mul hx k.1.2 ((Iwasawa.unipotent F n).inv_mem k.2.2)
end GroundTheory.Automorphic.Whittaker
