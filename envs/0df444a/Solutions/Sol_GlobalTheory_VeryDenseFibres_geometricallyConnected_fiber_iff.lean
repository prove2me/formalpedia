-- Prove2me | solution 1 for GlobalTheory.VeryDenseFibres.geometricallyConnected_fiber_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:50.024283+00:00
-- url     : https://prove2.me/submissions/cf9f90e1-66ee-48a6-8664-be7df72d8433

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Theorems.Thm_GlobalTheory_geometricallyConnected_of_isPullback_of_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.VeryDenseFibres
namespace GlobalTheory.VeryDenseFibres
theorem _root_.solution {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T) :
    GeometricallyConnected ((pullback.snd f t).fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine ⟨fun h => ?_, fun h => MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp h⟩
  have : Surjective (Spec.map (t.residueFieldMap y)) :=
    ⟨fun z => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hp
end GlobalTheory.VeryDenseFibres
