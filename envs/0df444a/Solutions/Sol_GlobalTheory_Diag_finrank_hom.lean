-- Prove2me | solution 1 for GlobalTheory.Diag.finrank_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:31.034702+00:00
-- url     : https://prove2.me/submissions/bd2f0365-e803-4dad-9899-87c30c498275

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_exists_isPullback

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
theorem _root_.solution (X : Type u) [AddCommGroup X] [Finite X] (s : S) :
    (splitTorus S X).hom.finrank s = Nat.card X := by
  obtain ⟨a, h⟩ := exists_isPullback X (toZ S)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X)))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X)))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ h]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X) _).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_eq_nat_card_basis (AddMonoidAlgebra.basis X ZU.{u})]
  rfl
end GlobalTheory.Diag
