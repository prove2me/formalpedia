-- Prove2me | solution 1 for GlobalTheory.flat_dvr_generic_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:00.157028+00:00
-- url     : https://prove2.me/submissions/3cf82899-1880-4ea2-998f-10bc6a9ab8b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Theorems.Thm_GlobalTheory_pullback_map_injective_of_flat
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_flat
import Theorems.Thm_GlobalTheory_isMonHom_of_pullback_of_flat
import Theorems.Thm_GlobalTheory_schemeTheoreticallyDominant_fractionField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X : Over (Sp T)), Flat Y.hom → IsSeparated X.hom → ∀ a b : Y ⟶ X, (Over.pullback (spMap (algebraMap T K))).map a = (Over.pullback (spMap (algebraMap T K))).map b → a = b) ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X Ga : Over (Sp T)) (io : Ga ⟶ X) (a : Y ⟶ X) (a' : (Over.pullback (spMap (algebraMap T K))).obj Y ⟶ (Over.pullback (spMap (algebraMap T K))).obj Ga), Flat Y.hom → IsClosedImmersion io.left → a' ≫ (Over.pullback (spMap (algebraMap T K))).map io = (Over.pullback (spMap (algebraMap T K))).map a → ∃! b : Y ⟶ Ga, b ≫ io = a ∧ (Over.pullback (spMap (algebraMap T K))).map b = a') ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'] (F : G ⟶ G'), Flat G.hom → IsSeparated G'.hom → IsMonHom ((Over.pullback (spMap (algebraMap T K))).map F) → IsMonHom F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T K _ _ _ _ _ _ Y X hY hX a b h
    have := schemeTheoreticallyDominant_fractionField T K
    exact pullback_map_injective_of_flat (spMap (algebraMap T K)) h
  · intro T K _ _ _ _ _ _ Y X Ga io a a' hY hio h
    have := schemeTheoreticallyDominant_fractionField T K
    exact existsUnique_lift_of_flat (spMap (algebraMap T K)) io a a' h
  · intro T K _ _ _ _ _ _ G G' _ _ F hG hG' hF
    have := schemeTheoreticallyDominant_fractionField T K
    exact isMonHom_of_pullback_of_flat (spMap (algebraMap T K)) F
end GlobalTheory
