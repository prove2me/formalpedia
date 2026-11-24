-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:04.535099+00:00
-- url     : https://prove2.me/submissions/70ebf5eb-dacf-4b1e-bb81-b6440f74fade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_section_of_unramified
import Theorems.Thm_GlobalTheory_isClosedImmersion_of_section_of_isSeparated

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
    [Etale f] [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  ⟨isOpenImmersion_of_section_of_unramified f s hs,
    isClosedImmersion_of_section_of_isSeparated f s hs⟩
end GlobalTheory
