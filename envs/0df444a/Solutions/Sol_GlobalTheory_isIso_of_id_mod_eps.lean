-- Prove2me | solution 1 for GlobalTheory.isIso_of_id_mod_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:52:50.157413+00:00
-- url     : https://prove2.me/submissions/61122482-afc9-43ea-b981-79e05d34e7c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
import Theorems.Thm_GlobalTheory_EpsIso_ker_fst_eq_span
import Theorems.Thm_GlobalTheory_EpsIso_bijective_of_mod_eps
import Theorems.Thm_GlobalTheory_EpsIso_fst_surjective
import Theorems.Thm_GlobalTheory_EpsIso_isHomeomorph_of_isPullback
import Theorems.Thm_GlobalTheory_EpsIso_isAffineHom_of_isHomeomorph
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_ker_app_eq_map_appLE_of_isPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  intro K _ Y Y' Z' q π π' j j' e h h' hfl hπ hj
  subst hπ hj
  obtain ⟨hcj, hhj⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h
  obtain ⟨hcj', hhj'⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h'
  have hcf : (⇑(j ≫ e) : Y → Z') = ⇑e ∘ ⇑j := rfl
  have hhe : IsHomeomorph e := by
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨e.continuous, ?_, ?_⟩
    · intro F hF
      have hF' : (⇑e) '' F = (⇑(j ≫ e)) '' ((⇑j) ⁻¹' F) := by
        rw [hcf, Set.image_comp, Set.image_preimage_eq _ hhj.surjective]
      rw [hF']
      exact hhj'.isClosedMap _ (hF.preimage j.continuous)
    · have hb := hhj'.bijective
      rw [hcf] at hb
      exact (Function.Bijective.of_comp_iff _ hhj.bijective).1 hb
  have hA : IsAffineHom e := GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph e hhe
  have hβ : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    GlobalTheory.EpsIso.fst_surjective K
  have hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom).hom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := GlobalTheory.EpsIso.ker_fst_eq_span K
  have hiso : ∀ W : Z'.Opens, IsAffineOpen W → IsIso (e.app W) := by
    intro W hW
    have hW' : IsAffineOpen (e ⁻¹ᵁ W) := IsAffineHom.isAffine_preimage W hW
    have hcomp : (e ≫ π').appLE ⊤ (e ⁻¹ᵁ W) le_top = π'.appLE ⊤ W le_top ≫ e.app W := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE ..).symm
    have hB := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h' hW
    have hC := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h hW'
    rw [hker, Ideal.map_span, Set.image_singleton] at hB hC
    have hC' := hC.trans (congrArg
      (fun g => Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ g).hom DualNumber.eps}) hcomp)
    have hfl' := HasRingHomProperty.appLE @Flat (e ≫ π') hfl ⟨⊤, isAffineOpen_top _⟩ ⟨e ⁻¹ᵁ W, hW'⟩ le_top
    have hfl2 := (congrArg (fun g => g.hom.Flat) hcomp).mp hfl'
    have hg : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    have hflat : ((e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
        π'.appLE ⊤ W le_top).hom).Flat := by
      have heq : (e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
          π'.appLE ⊤ W le_top).hom = (π'.appLE ⊤ W le_top ≫ e.app W).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom := by
        exact RingHom.ext fun x => rfl
      rw [heq]
      exact RingHom.Flat.comp hg hfl2
    have := hcj'
    have hbij := GlobalTheory.EpsIso.bijective_of_mod_eps
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom
      (e.app W).hom ((j ≫ e).app W).hom (j.app (e ⁻¹ᵁ W)).hom (fun b => rfl)
      (Scheme.Hom.app_surjective (j ≫ e) W hW) hflat hB hC'
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{0})
    (fun V : Z'.affineOpens => V.1) (iSup_affineOpens_eq_top Z') fun V => ?_
  have hsrc : IsAffine (e ⁻¹ᵁ V.1) := IsAffineHom.isAffine_preimage _ V.2
  have htgt : IsAffine V.1 := V.2
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (e ∣_ V.1))).mpr ?_
  rw [MorphismProperty.isomorphisms.iff, morphismRestrict_appTop]
  have hV : IsAffineOpen (V.1.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have hb1 : Function.Bijective (e.app (V.1.ι ''ᵁ ⊤)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (hiso _ hV)
  have hb2 : Function.Bijective
      (Y'.presheaf.map (eqToHom (image_morphismRestrict_preimage e V.1 ⊤)).op).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact isIso_SpecMap_iff.2 (hb2.comp hb1)
end GlobalTheory
