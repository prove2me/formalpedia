-- Prove2me | solution 1 for GlobalTheory.bijective_restrictPoints_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:11.01526+00:00
-- url     : https://prove2.me/submissions/6bf24f49-d790-4653-81d2-39de61067a4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale
import Theorems.Thm_GlobalTheory_bijective_restrictPoints_of_existsUnique

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
theorem _root_.solution {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (h : T ⟶ S) (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker) :
    Function.Bijective (restrictPoints f h i) :=
  bijective_restrictPoints_of_existsUnique f h i fun g w ↦ existsUnique_lift_of_etale f i hi g h w
end GlobalTheory
