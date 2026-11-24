-- Prove2me | solution 1 for GlobalTheory.RedPts.toSec_left_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.201817+00:00
-- url     : https://prove2.me/submissions/2b3970f6-c1e1-4260-a877-f59d77147df4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOneOfPowOfClosedPoint

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
noncomputable section
open GlobalTheory GlobalTheory.RedPts
variable {S : Scheme.{0}}
namespace GlobalTheory.RedPts
theorem _root_.solution (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) (x : Over.mk p ⟶ G) :
    (toSec G p x).left ≫ pullback.fst G.hom p = x.left := by
  have h₁ : ((Over.pullback p).map x).left ≫ pullback.fst G.hom p = pullback.fst p p ≫ x.left :=
    pullback.lift_fst _ _ _
  have h₂ : (diagSec p).left ≫ pullback.fst p p = 𝟙 T := pullback.lift_fst _ _ _
  change ((diagSec p).left ≫ ((Over.pullback p).map x).left) ≫ _ = _
  rw [Category.assoc, h₁]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) h₂)).trans (Category.id_comp _)
end GlobalTheory.RedPts
