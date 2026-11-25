-- Prove2me | solution 1 for GlobalTheory.Diag.finrank_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:27.667895+00:00
-- url     : https://prove2.me/submissions/f14d226d-a496-4acb-97a1-cc8bc08a892d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_finrank_diagMap
import Theorems.Thm_GlobalTheory_Diag_nsmul_injective
import Theorems.Thm_GlobalTheory_Diag_finiteIndex_nsmul

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
variable (X : Type u) [AddCommGroup X] {n : ℕ}
namespace GlobalTheory.Diag
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X] (hn : n ≠ 0)
    (y : (splitTorus S X).left) :
    (mulN (splitTorus S X) n).left.finrank y = n ^ Module.finrank ℤ X := by
  have := finiteIndex_nsmul X hn
  rw [mulN_eq_diagMap, finrank_diagMap S (nsmul_injective X hn), AddSubgroup.index_range_nsmul]
end GlobalTheory.Diag
