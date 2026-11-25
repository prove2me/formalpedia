-- Prove2me | solution 1 for GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:24.454486+00:00
-- url     : https://prove2.me/submissions/5f4689e4-dd59-4580-843c-89387c6ae365

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field
import Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), Smooth p → IsProper p →
      GeometricallyConnected p → Function.Bijective p.appTop.hom := by
  intro K _ X p hs hp hg

  haveI := hs
  haveI := hp
  haveI := hg
  haveI : GeometricallyIntegral p :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X _ p hs hg
  haveI : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  exact ConcreteCategory.bijective_of_isIso p.appTop
end GlobalTheory
