-- Prove2me | solution 1 for GlobalTheory.MultiplicativeReduction.isProper_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:25.944983+00:00
-- url     : https://prove2.me/submissions/553304fb-a81c-4ea2-a197-d4e5b16a8070

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyTorusExtensionSplitTorus
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MultiplicativeReduction
open GlobalTheory.WeierstrassCurve
namespace GlobalTheory.MultiplicativeReduction
theorem _root_.solution {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    {K : Type} [Field K] (f : R →+* K) (hΔ : f W.Δ ≠ 0) :
    IsProper (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f))) := by
  have hpb : IsPullback (mapHom W f rfl ∣_ U) ((mapHom W f rfl ⁻¹ᵁ U).ι ≫ toSpec (W.map f))
      (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  have htop : mapHom W f rfl ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    let k := (scheme (W.map f)).residueField x
    obtain ⟨ρ, P, h, hx⟩ : ∃ (ρ : K →+* k) (P : Fin 3 → k)
        (h : IsUnimodularSol ((W.map f).map ρ) P),
        (scheme (W.map f)).fromSpecResidueField x = ptHom (W.map f) ρ P h := by
      obtain ⟨g, hg⟩ := Spec.map_surjective
        ((scheme (W.map f)).fromSpecResidueField x ≫ toSpec (W.map f))
      exact ⟨g.hom, exists_eq_ptHom (W.map f) (A := k) g.hom _ hg.symm⟩
    have hE : ((W.map f).map ρ).IsElliptic := ⟨by
      rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
      exact (IsUnit.mk0 _ hΔ).map ρ⟩
    have h1 := (hU k (ρ.comp f) P (h.comp_of_map_eq rfl)).mpr h.nonsingular
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage, ← hx] at h1
    have h2 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) ∈
        mapHom W f rfl ⁻¹ᵁ U := h1 (Set.mem_univ (IsLocalRing.closedPoint k))
    have h3 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) = x :=
      Scheme.fromSpecResidueField_apply x _
    exact h3 ▸ h2
  have : IsIso (mapHom W f rfl ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Scheme.topIso _).hom)
  rw [← hpb.isoPullback_inv_snd]
  infer_instance
end GlobalTheory.MultiplicativeReduction
