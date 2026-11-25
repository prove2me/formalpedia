-- Prove2me | solution 1 for GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:28:55.494327+00:00
-- url     : https://prove2.me/submissions/ee6c0402-cf54-4485-b656-a5600095346f

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
theorem _root_.solution (O K : Type*) [CommRing O]
    [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨g, hg, hdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective _ IsLocalRing.residue_surjective p) hp
  have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hgm
  have hd : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hdeg]
    exact_mod_cast (Irreducible.natDegree_pos hirr).ne'
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero hd
  exact ⟨IsLocalRing.residue O r, by rw [← hg, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]⟩
end GlobalTheory
