-- Prove2me | solution 1 for GlobalTheory.Diag.baseChangeIso_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:49.009872+00:00
-- url     : https://prove2.me/submissions/919ef09e-60c3-46b4-aa01-6382583f9d17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory GlobalTheory.Diag
variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable {S} {S' : Scheme.{u}} (f : S' ⟶ S)
namespace GlobalTheory.Diag
theorem _root_.solution (u : Y →+ X) :
    (Over.pullback f).map (diagMap S u) ≫ (baseChangeIso f Y).hom =
      (baseChangeIso f X).hom ≫ diagMap S' u := by
  ext1
  apply (isPullback_torusFst S' Y).hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, diagMap_left_torusFst,
      baseChangeIso_hom_torusFst, reassoc_of% baseChangeIso_hom_torusFst f X, ← diagMap_left_torusFst]
    exact pullback.lift_fst_assoc _ _ _ _ |>.trans (Category.assoc _ _ _)
  · rw [Over.w, Over.w]
end GlobalTheory.Diag
