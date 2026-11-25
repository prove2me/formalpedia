-- Prove2me | solution 1 for GlobalTheory.Diag.finrank_diagMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:19.33761+00:00
-- url     : https://prove2.me/submissions/70ad688d-adcc-4964-b64e-a35e3319529d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_flat_ringMap
import Theorems.Thm_GlobalTheory_Diag_isFinite_ringMap
import Theorems.Thm_GlobalTheory_GroupAlg_faithfullyFlat_of_injective
import Theorems.Thm_GlobalTheory_GroupAlg_finite_of_finiteIndex
import Theorems.Thm_GlobalTheory_GroupAlg_finrank_of_injective


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
namespace GlobalTheory.Diag
theorem _root_.solution {u : Y →+ X} (hu : Function.Injective u) [u.range.FiniteIndex]
    (y : (splitTorus S Y).left) : (diagMap S u).left.finrank y = u.range.index := by
  have := flat_ringMap hu
  have := isFinite_ringMap u
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_diagMap S u),
    Scheme.Hom.finrank_SpecMap_eq_finrank (GroupAlg.finite_of_finiteIndex _ u)
      (GroupAlg.faithfullyFlat_of_injective _ u hu).flat]
  exact GroupAlg.finrank_of_injective _ u hu _
end GlobalTheory.Diag
