-- Prove2me | solution 1 for GlobalTheory.GeomFibre.bijective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:45.00183+00:00
-- url     : https://prove2.me/submissions/c254da32-572a-40bd-add5-8afe10cf5823

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFieldPullbackAppTopBijectiveAndTriv

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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.GeomFibre
namespace GlobalTheory.GeomFibre
theorem _root_.solution (K : Type) [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] : Function.Bijective f.appTop.hom := by
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed K f
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  have hfin' : (f.appTop.hom.comp e.hom).Finite := hfin.comp (RingHom.Finite.of_surjective _ he.2)
  have hb : Function.Bijective (f.appTop.hom.comp e.hom) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (k := K) _ hfin'.to_isIntegral
  exact (Function.Bijective.of_comp_iff _ he).1 hb
end GlobalTheory.GeomFibre
