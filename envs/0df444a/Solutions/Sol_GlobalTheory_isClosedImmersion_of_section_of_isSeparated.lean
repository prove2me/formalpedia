-- Prove2me | solution 1 for GlobalTheory.isClosedImmersion_of_section_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:49.446514+00:00
-- url     : https://prove2.me/submissions/83033967-b1eb-4116-8df4-45fb3cec83e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : IsClosedImmersion s :=
  have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
  .of_comp s f
end GlobalTheory
