-- Prove2me | solution 1 for GlobalTheory.existsUnique_closureLift_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:30.988831+00:00
-- url     : https://prove2.me/submissions/dcd183fd-1587-48cf-b36f-16ef933bd5b9

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
theorem _root_.solution {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : Function.Injective φ.hom) (t : Spec R ⟶ P) (w : Spec R' ⟶ W)
    (h : Spec.map φ ≫ t = w ≫ j) : ∃! l : Spec R ⟶ j.image, l ≫ j.imageι = t :=
  have := (schemeDominant_specMap_iff φ).mpr hφ
  existsUnique_closureLift j t _ w h
end GlobalTheory
