-- Prove2me | solution 1 for GlobalTheory.splits_of_monic_of_valuationRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:19.91747+00:00
-- url     : https://prove2.me/submissions/89518fd6-ebfc-4d21-8320-99202aa435be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingHenselianAndSmoothPointsLift

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
theorem _root_.solution (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    {f : Polynomial O} (hf : f.Monic) : f.Splits := by
  refine Polynomial.Splits.of_splits_map_of_injective (IsFractionRing.injective O K)
    (IsAlgClosed.splits _) fun a ha => ?_
  have hroot : Polynomial.eval₂ (algebraMap O K) a f = 0 := by
    rw [Polynomial.mem_roots (hf.map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map] at ha
    exact ha
  have hint : IsIntegral O a := ⟨f, hf, hroot⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨b, hb⟩
end GlobalTheory
