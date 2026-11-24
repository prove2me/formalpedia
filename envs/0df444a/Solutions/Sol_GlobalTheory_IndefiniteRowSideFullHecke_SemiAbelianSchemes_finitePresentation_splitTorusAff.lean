-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.finitePresentation_splitTorusAff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:18.576138+00:00
-- url     : https://prove2.me/submissions/519bc912-4e69-4031-ac97-826962c35df3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
open ReciprocityTheory.ChartRestriction.G.Semi
variable (X : Type u) [AddCommGroup X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
theorem _root_.solution [Module.Finite ℤ X] :
    LocallyOfFinitePresentation (splitTorusAff ZU X).hom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ZU (torusRing ZU X))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  exact Algebra.FinitePresentation.of_finiteType.1 inferInstance
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
