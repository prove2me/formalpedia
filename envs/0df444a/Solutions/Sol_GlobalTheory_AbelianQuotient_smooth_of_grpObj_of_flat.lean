-- Prove2me | solution 1 for GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:41.666394+00:00
-- url     : https://prove2.me/submissions/67e8953d-e2ea-4541-99db-f30f4e4f7bb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme

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
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}
namespace GlobalTheory.AbelianQuotient
theorem _root_.solution (Q : Over S) [GrpObj Q] [Flat Q.hom]
    [LocallyOfFinitePresentation Q.hom] [GeometricallyReduced Q.hom] : Smooth Q.hom := by
  refine Smooth.of_smooth_fiberToSpecResidueField _ fun y => ?_
  letI : GrpObj (Over.mk Q.hom) := inferInstanceAs (GrpObj Q)
  letI : GrpObj (Over.mk (pullback.snd Q.hom (S.fromSpecResidueField y))) :=
    Over.grpObjMkPullbackSnd
  exact smooth_of_grpObj (K := S.residueField y) (pullback.snd Q.hom (S.fromSpecResidueField y))
end GlobalTheory.AbelianQuotient
