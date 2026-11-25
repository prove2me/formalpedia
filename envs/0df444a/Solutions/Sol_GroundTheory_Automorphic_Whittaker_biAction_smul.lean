-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.biAction_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:17.671149+00:00
-- url     : https://prove2.me/submissions/607852a3-98ac-44be-93a8-b4048f40211b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution

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
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : NN F n) (g : GL (Fin n) F) :
    h • g = (h.1 : GL (Fin n) F) * g * (h.2 : GL (Fin n) F)⁻¹ := rfl
end GroundTheory.Automorphic.Whittaker
