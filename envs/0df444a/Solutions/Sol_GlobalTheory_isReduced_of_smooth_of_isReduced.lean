-- Prove2me | solution 1 for GlobalTheory.isReduced_of_smooth_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:06.638787+00:00
-- url     : https://prove2.me/submissions/f6b9ca1d-51f6-4e27-b17f-c3b5862429e8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Theorems.Thm_GlobalTheory_isReduced_algebra_of_smooth_of_isReduced
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
private theorem isReduced_of_smooth_of_isAffine_of_isReduced {Y T : Scheme.{0}} (g : Y ⟶ T) [Smooth g]
    [IsAffine T] [IsReduced T] : IsReduced Y := by
  have hι : ∀ j, Smooth (Y.affineOpenCover.f j) := fun j => inferInstance
  refine @IsReduced.of_openCover _ Y.affineOpenCover.openCover (fun j => ?_)

  have h₁ : Smooth (g ≫ T.isoSpec.hom) := inferInstance
  have h₂ : Smooth (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom) :=
    MorphismProperty.comp_mem _ _ _ (hι j) h₁
  have hs : Smooth (Spec.map (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom))) := by
    rw [Spec.map_preimage]; exact h₂
  let := (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)).hom.toAlgebra
  have : Algebra.Smooth Γ(T, ⊤) (Y.affineOpenCover.X j) := HasRingHomProperty.Spec_iff.mp hs
  have : _root_.IsReduced (Y.affineOpenCover.X j) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced Γ(T, ⊤) (Y.affineOpenCover.X j)
  show IsReduced (Spec (Y.affineOpenCover.X j))
  infer_instance
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] [IsReduced S] : IsReduced X := by

  have hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨V, hV⟩ : ∃ V : S.affineOpens, f x ∈ (V : S.Opens) := by
      have hx : f x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hx
    have : IsAffine (V : S.Opens) := V.2
    have hU : IsReduced (f ⁻¹ᵁ (V : S.Opens)) :=
      isReduced_of_smooth_of_isAffine_of_isReduced (f ∣_ (V : S.Opens))
    let y : (f ⁻¹ᵁ (V : S.Opens) : X.Opens) := ⟨x, hV⟩
    have := @isReduced_stalk_of_isReduced _ hU y
    exact isReduced_of_injective (Scheme.Opens.stalkIso _ y).symm.commRingCatIsoToRingEquiv
      (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X
end GlobalTheory
