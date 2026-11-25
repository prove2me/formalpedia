-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:12:21.185502+00:00
-- url     : https://prove2.me/submissions/fcf0bd0d-9586-4012-b421-bfe33ca74bff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_generic_of_isGrpPullback

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
    {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U}
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (e : G' ≅ H') [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ e.hom.left ≫ ψ = φ ≫ E.hom.left := by
  obtain ⟨E₁, ⟨h₁, c₁⟩, u₁⟩ := generic_of_isGrpPullback h hS hj hG hH hφ hψ e.hom
  obtain ⟨E₂, ⟨h₂, c₂⟩, -⟩ := generic_of_isGrpPullback h hS hj hH hG hψ hφ e.inv
  obtain ⟨FG, -, uG⟩ := generic_of_isGrpPullback h hS hj hG hG hφ hφ (𝟙 G')
  obtain ⟨FH, -, uH⟩ := generic_of_isGrpPullback h hS hj hH hH hψ hψ (𝟙 H')
  have k₁ : E₁ ≫ E₂ = 𝟙 G := by
    rw [uG (E₁ ≫ E₂) ⟨inferInstance, by rw [Over.comp_left, ← Category.assoc, ← c₁, Category.assoc, ← c₂,
      ← Category.assoc, ← Over.comp_left, e.hom_inv_id]⟩, uG (𝟙 G) ⟨inferInstance, by simp⟩]
  have k₂ : E₂ ≫ E₁ = 𝟙 H := by
    rw [uH (E₂ ≫ E₁) ⟨inferInstance, by rw [Over.comp_left, ← Category.assoc, ← c₂, Category.assoc, ← c₁,
      ← Category.assoc, ← Over.comp_left, e.inv_hom_id]⟩, uH (𝟙 H) ⟨inferInstance, by simp⟩]
  refine ⟨⟨E₁, E₂, k₁, k₂⟩, ⟨h₁, c₁⟩, ?_⟩
  rintro E ⟨hE, cE⟩
  exact Iso.ext (u₁ E.hom ⟨hE, cE⟩)
end GlobalTheory.Published.SemiAbelianHomExtension
