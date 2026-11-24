-- Prove2me | solution 1 for GlobalTheory.VVRank.surjective_mulT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:07.233728+00:00
-- url     : https://prove2.me/submissions/0978901b-3bf5-41fe-b5c8-71ccea895443

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution (n : ℕ) (h : Surjective (mulA A n).left) (T : Over S) :
    Surjective (mulT A T n).left := by
  have e₁ : (mulT A T n).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, mulT, lift_fst]
  have e₂ : (snd T A).left ≫ (mulA A n).left = (mulT A T n).left ≫ (snd T A).left := by
    rw [← Over.comp_left, ← Over.comp_left, mulT, lift_snd, MonObj.comp_pow, Category.comp_id]
  have hp : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom A.hom).flip
  have : IsPullback (snd T A).left (mulT A T n).left (mulA A n).left (snd T A).left := by
    refine IsPullback.of_bot ?_ e₂ hp
    rw [e₁, Over.w]
    exact hp
  exact MorphismProperty.of_isPullback (P := @Surjective) this h
end GlobalTheory.VVRank
