-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso_of_extensions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:39.524675+00:00
-- url     : https://prove2.me/submissions/6ae8f8b4-dee6-4389-ba9a-50d781053e25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_generic_existsUnique_iso_of_isGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hj : IsGenericPointHom j)
    {A : Over U} [GrpObj A] {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ H.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A H j ψ) :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ φ ≫ E.hom.left = ψ := by
  have _ : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨E, ⟨hE, cE⟩, uE⟩ :=
    generic_existsUnique_iso_of_isGrpPullback h hS hj hG hH hφ hψ (Iso.refl A)
  simp only [Iso.refl_hom, Over.id_left, Category.id_comp] at cE uE
  exact ⟨E, ⟨hE, cE.symm⟩, fun E' ⟨hE', cE'⟩ => uE E' ⟨hE', cE'.symm⟩⟩
end GlobalTheory.Published.SemiAbelianHomExtension
