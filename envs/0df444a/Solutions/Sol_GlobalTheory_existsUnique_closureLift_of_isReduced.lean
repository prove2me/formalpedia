-- Prove2me | solution 1 for GlobalTheory.existsUnique_closureLift_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:34.638569+00:00
-- url     : https://prove2.me/submissions/05d9c137-fbd9-4125-977c-e77f0e25d846

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_existsUnique_closureLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)
namespace GlobalTheory
theorem _root_.solution (t : T ⟶ P) (d : T' ⟶ T) [IsReduced T]
    [IsDominant d] (w : T' ⟶ W) (h : d ≫ t = w ≫ j) :
    ∃! l : T ⟶ j.image, l ≫ j.imageι = t :=
  have := IsSchemeTheoreticallyDominant.of_isDominant d
  existsUnique_closureLift j t d w h
end GlobalTheory
