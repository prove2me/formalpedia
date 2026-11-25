-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.chi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:03.883826+00:00
-- url     : https://prove2.me/submissions/832f914b-a0fd-4902-b0c9-5b9446dbd298

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
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : NN F n) :
    chi ψ₀ h = psiN ψ₀ (h.1 : GL (Fin n) F) * (psiN ψ₀ (h.2 : GL (Fin n) F))⁻¹ := rfl
end GroundTheory.Automorphic.Whittaker
