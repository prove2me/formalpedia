-- Prove2me | solution 1 for GlobalTheory.T.group_laws_on_cover_agree_on_common_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:58.891805+00:00
-- url     : https://prove2.me/submissions/893fdd02-d945-45b4-9313-740f6a72e738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPointsStatement
import Theorems.Thm_GlobalTheory_CoverOpCompat_opCompat


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
open GlobalTheory.ZM
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  first | exact @GlobalTheory.CoverOpCompat.opCompat | exact GlobalTheory.CoverOpCompat.opCompat | (intros; apply GlobalTheory.CoverOpCompat.opCompat <;> assumption)
end _root_.GlobalTheory.T
