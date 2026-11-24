-- Prove2me | solution 1 for GlobalTheory.flat_closure_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:21.653806+00:00
-- url     : https://prove2.me/submissions/7ba7d7b8-f44c-421a-ad1d-1e438f82d1cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
import Theorems.Thm_GlobalTheory_exists_grpObj_of_flat_closed
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
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (P Ga : Over (Sp T)) [GrpObj P] (io : Ga ⟶ P) (Z : Over (Sp K)) [GrpObj Z] (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj P) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left → Flat Ga.hom → IsMonHom i → e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io → ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  intro T K _ _ _ _ _ _ P Ga _ io Z _ i e _ _ _ h
  have := schemeTheoreticallyDominant_fractionField T K
  exact exists_grpObj_of_flat_closed _ P Ga io Z i e h
end GlobalTheory
