-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigmaL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:54.241501+00:00
-- url     : https://prove2.me/submissions/809b6dca-b0bd-440e-904b-8fb856f5805c

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
variable [TopologicalSpace F] [IsTopologicalRing F]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (f : GL (Fin n) F → ℂ) (x : GL (Fin n) F) : sigmaL f x = f (sigma x) := rfl
end GroundTheory.Automorphic.Whittaker
