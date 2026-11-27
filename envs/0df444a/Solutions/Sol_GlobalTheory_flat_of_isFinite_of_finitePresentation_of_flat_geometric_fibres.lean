-- Prove2me | solution 1 for GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:42.75252+00:00
-- url     : https://prove2.me/submissions/ffcfc321-887c-49e0-ae1b-998447cc5f9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Theorems.Thm_GlobalTheory_FinitePresFibreFlat_flat_of_flatOver_fields
import Theorems.Thm_GlobalTheory_FibreFlat_flatOver_of_pullback
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flatOver_descend
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flat_of_flatOver_fields


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S X Y f h1 h0 h2 h3 H
  refine FinitePresFibreFlat.flat_of_flatOver_fields f.left Y.hom h2 (by rwa [Over.w])
    (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))
end GlobalTheory
