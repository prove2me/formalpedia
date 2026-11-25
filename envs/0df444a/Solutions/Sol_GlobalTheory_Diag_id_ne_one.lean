-- Prove2me | solution 1 for GlobalTheory.Diag.id_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:12:40.726563+00:00
-- url     : https://prove2.me/submissions/42ad7f18-37de-4c09-9777-66451431605c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_diagMap_injective

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
theorem _root_.solution [Nonempty S] [Nontrivial X] : 𝟙 (splitTorus S X) ≠ 1 := by
  rw [← diagMap_id, ← diagMap_zero]
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  exact hx (DFunLike.congr_fun (diagMap_injective S h) x)
end GlobalTheory.Diag
