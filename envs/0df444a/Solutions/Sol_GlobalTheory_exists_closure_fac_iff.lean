-- Prove2me | solution 1 for GlobalTheory.exists_closure_fac_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:38.277614+00:00
-- url     : https://prove2.me/submissions/8df1f325-ff87-462b-a444-039505b902a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

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
theorem _root_.solution (t : T ⟶ P) :
    (∃ l : T ⟶ j.image, l ≫ j.imageι = t) ↔ j.ker ≤ t.ker := by
  constructor
  · rintro ⟨l, rfl⟩
    simpa using l.le_ker_comp j.imageι
  · exact fun h ↦ ⟨IsClosedImmersion.lift j.imageι t (by simpa using h),
      IsClosedImmersion.lift_fac _ _ _⟩
end GlobalTheory
