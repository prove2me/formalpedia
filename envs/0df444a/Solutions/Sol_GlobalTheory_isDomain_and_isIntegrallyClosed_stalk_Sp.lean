-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:36.594151+00:00
-- url     : https://prove2.me/submissions/4c7a9185-de8d-47dc-9cae-8717ed1709a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isDomain


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
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (y : Sp A) :
    IsDomain ((Sp A).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp A).presheaf.stalk y) := by
  have hy : (y.asIdeal : Ideal A).IsPrime := y.isPrime
  let _ : Algebra A ((Sp A).presheaf.stalk y) := StructureSheaf.stalkAlgebra A y
  have : IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A) :=
    StructureSheaf.IsLocalization.to_stalk A y
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A)
    ((Sp A).presheaf.stalk y)
end GlobalTheory
