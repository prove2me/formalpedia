-- Prove2me | solution 1 for GlobalTheory.Diag.etale_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:17.934101+00:00
-- url     : https://prove2.me/submissions/63baa1dc-1ccc-467d-acbe-6bfe3450504f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_exists_isPullback
import Theorems.Thm_GlobalTheory_GroupAlg_etale_of_isUnit_card


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
theorem _root_.solution (X : Type u) [AddCommGroup X] [Finite X] (h : IsUnit (Nat.card X : Γ(S, ⊤))) :
    Etale (splitTorus S X).hom := by
  obtain ⟨a, ha⟩ := exists_isPullback (R := Γ(S, ⊤)) X S.toSpecΓ
  refine MorphismProperty.of_isPullback (P := @Etale) ha
    ((HasRingHomProperty.Spec_iff (P := @Etale)).2 ?_)
  exact RingHom.etale_algebraMap.2 (GroupAlg.etale_of_isUnit_card _ h)
end GlobalTheory.Diag
