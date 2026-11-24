-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_pullback_grp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:17:57.433826+00:00
-- url     : https://prove2.me/submissions/986667ba-fe33-4ad6-a449-fa8e3ac5a873

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit
namespace GlobalTheory.SS.LiftTorus
theorem _root_.solution {C : Type*} [Category C] [CartesianMonoidalCategory C] [HasPullbacks C]
    {G B H : C} [GrpObj G] [GrpObj B] [GrpObj H] (q : G ⟶ B) (f : H ⟶ B) [IsMonHom q] [IsMonHom f] :
    ∃ (E : C) (_ : GrpObj E) (p : E ⟶ G) (r : E ⟶ H), IsMonHom p ∧ IsMonHom r ∧ IsPullback p r q f := by
  let q' : Grp.mk G ⟶ Grp.mk B := Grp.homMk q
  let f' : Grp.mk H ⟶ Grp.mk B := Grp.homMk f
  have h := (IsPullback.of_hasPullback q' f').map (Grp.forget C)
  exact ⟨(pullback q' f').X, inferInstance, (pullback.fst q' f').hom.hom, (pullback.snd q' f').hom.hom,
    inferInstance, inferInstance, h⟩
end GlobalTheory.SS.LiftTorus
