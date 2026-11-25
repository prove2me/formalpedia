-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:05.035142+00:00
-- url     : https://prove2.me/submissions/0ee37b32-f85c-4d58-ba6a-879e19d494e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_quasiCompact_and_dominant
import Theorems.Thm_GlobalTheory_ExtUnique_flat_and_isSeparated_of_isSemiAbelian
import Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_left_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  let V : S.Opens := j.opensRange
  have hV : Dense (V : Set S) := j.denseRange
  let e : V.toScheme ⟶ U := j.isoOpensRange.inv
  have he : e ≫ j = V.ι := j.isoOpensRange_inv_comp
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G V.ι)
    (((isGrpPullback_pullback G' e).comp hφ).congr he rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (((isGrpPullback_pullback H' e).comp hψ).congr he rfl)
    (isGrpPullback_pullback H V.ι)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h S hS V hV G H hG hH (a.hom ≫ (Over.pullback e).map f ≫ b.hom) inferInstance
  have key : f.left ≫ ψ = φ ≫ F.left := by
    have h₁ := pullback_map_left_fst V.ι F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc,
      ← Category.assoc ((Over.pullback e).map f).left, pullback_map_left_fst, Category.assoc,
      Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi (pullback.fst G'.hom e)).1 ((cancel_epi a.hom.left).1 h₁)
  exact ⟨F, ⟨hF, key⟩, fun F' hF' => over_hom_ext_of_isPullback hφ.1 (hF'.2.symm.trans key)⟩
end GlobalTheory.Published.SemiAbelianHomExtension
