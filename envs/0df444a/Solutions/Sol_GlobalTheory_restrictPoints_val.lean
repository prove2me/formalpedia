-- Prove2me | solution 1 for GlobalTheory.restrictPoints_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:00.373163+00:00
-- url     : https://prove2.me/submissions/2c8d5fec-0bad-4758-a1e3-9beb65a838c4

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
theorem _root_.solution {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S) (i : T₀ ⟶ T)
    (l : {l : T ⟶ X // l ≫ f = h}) : (restrictPoints f h i l).1 = i ≫ l.1 := rfl
end GlobalTheory
