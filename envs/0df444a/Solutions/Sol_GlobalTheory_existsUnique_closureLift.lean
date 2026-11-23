-- Prove2me | solution 1 for GlobalTheory.existsUnique_closureLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:13.700801+00:00
-- url     : https://prove2.me/submissions/e3dcccb9-72e7-479f-87d9-7c6dd551db39

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
theorem _root_.solution (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : ∃! l : T ⟶ j.image, l ≫ j.imageι = t :=
  ⟨closureLift j t d w h, closureLift_imageι j t d w h,
    fun _ hl ↦ closure_hom_ext j (hl.trans (closureLift_imageι j t d w h).symm)⟩
end GlobalTheory
