-- Prove2me | solution 1 for GlobalTheory.henselianLocalRing_of_valuationRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:39.038979+00:00
-- url     : https://prove2.me/submissions/0ae23ce2-26e5-4664-a0e1-0286eb070f51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingHenselianAndSmoothPointsLift
import Theorems.Thm_GlobalTheory_splits_of_monic_of_valuationRing_of_isAlgClosed

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
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    HenselianLocalRing O where
  is_henselian f hf a₀ h₁ _ := by
    have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hf
    rw [hs.eval_eq_prod_roots_of_monic hf a₀,
      (IsLocalRing.maximalIdeal.isMaximal O).isPrime.multiset_prod_mem_iff_exists_mem] at h₁
    obtain ⟨c, hc, hcm⟩ := h₁
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hc
    refine ⟨r, (Polynomial.mem_roots hf.ne_zero).mp hr, ?_⟩
    rw [← neg_sub]
    exact neg_mem hcm
end GlobalTheory
