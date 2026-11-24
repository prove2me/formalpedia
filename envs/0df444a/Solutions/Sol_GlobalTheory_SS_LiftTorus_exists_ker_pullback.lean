-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_ker_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:17:56.580122+00:00
-- url     : https://prove2.me/submissions/2d52bc82-a86b-4c2b-b2c6-1f897f39b7b6

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
theorem _root_.solution {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B H E : C} [GrpObj T] [GrpObj G] [GrpObj B] [GrpObj H] [GrpObj E] {i : T ⟶ G} {q : G ⟶ B}
    {f : H ⟶ B} {p : E ⟶ G} {r : E ⟶ H} [IsMonHom i] [IsMonHom f] [IsMonHom p] [IsMonHom r]
    (hi : IsPullback i (toUnit _) q η[B]) (h : IsPullback p r q f) :
    ∃ j : T ⟶ E, IsMonHom j ∧ IsPullback j (toUnit _) r η[H] := by
  have w : i ≫ q = (toUnit T ≫ η[H]) ≫ f := by
    rw [hi.w, Category.assoc, IsMonHom.one_hom]
  refine ⟨h.lift i _ w, ⟨h.hom_ext ?_ ?_, h.hom_ext ?_ ?_⟩, ?_⟩
  · simp
  · simp
  · simp [tensorHom_comp_tensorHom_assoc]
  · simp only [Category.assoc, h.lift_snd, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]
  · refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [h.lift_fst, IsMonHom.one_hom]
    exact hi
end GlobalTheory.SS.LiftTorus
