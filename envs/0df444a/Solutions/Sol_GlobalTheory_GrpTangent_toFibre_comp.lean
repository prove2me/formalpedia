-- Prove2me | solution 1 for GlobalTheory.GrpTangent.toFibre_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:20.185531+00:00
-- url     : https://prove2.me/submissions/39049617-9b2f-4ce5-8bcb-6bba56cfca90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
variable {k : Type} [CommRing k] (p : Sp k ⟶ S)
namespace GlobalTheory.GrpTangent
theorem _root_.solution {X Y : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) (f : X ⟶ Y) :
    toFibre p (w ≫ f) = toFibre p w ≫ (Over.pullback p).map f := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have : ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left :=
    pullback.lift_fst _ _ _
  rw [toFibre_left_fst, Over.comp_left, Over.comp_left, Category.assoc, this,
    toFibre_left_fst_assoc]
end GlobalTheory.GrpTangent
