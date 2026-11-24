-- Prove2me | solution 1 for GlobalTheory.GrpTangent.toFibre_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:57.771915+00:00
-- url     : https://prove2.me/submissions/d1243a62-9db8-4c49-bf05-9f380d2e82d1

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
theorem _root_.solution {X : Over S} : Function.Surjective (toFibre p (X := X)) := fun w =>
  ⟨Over.homMk (w.left ≫ pullback.fst X.hom p) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ p) (Over.w w)),
    Over.OverMorphism.ext (pullback.hom_ext (toFibre_left_fst p _)
      ((Over.w _).trans (Over.w w).symm))⟩
end GlobalTheory.GrpTangent
