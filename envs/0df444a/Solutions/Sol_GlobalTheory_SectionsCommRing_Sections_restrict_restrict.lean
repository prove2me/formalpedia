-- Prove2me | solution 1 for GlobalTheory.SectionsCommRing.Sections.restrict_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:37.021256+00:00
-- url     : https://prove2.me/submissions/cb7446c7-96d5-4ae8-b9d6-63b37e55718e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.SectionsCommRing
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
open GlobalTheory.SectionsCommRing.Sections
variable (s : X ⟶ Spec (CommRingCat.of R))
namespace GlobalTheory.SectionsCommRing.Sections
theorem _root_.solution {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (a : Sections s U) :
    restrict s k (restrict s h a) = restrict s (k.trans h) a := by
  show ((X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom a) =
    (X.presheaf.map (homOfLE (k.trans h)).op).hom a
  rw [← X.presheaf.map_comp]
  rfl
end GlobalTheory.SectionsCommRing.Sections
