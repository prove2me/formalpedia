-- Prove2me | solution 1 for GlobalTheory.torusExtension_smooth_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:10:45.444891+00:00
-- url     : https://prove2.me/submissions/d9090cfc-f294-4e25-a5f5-9946106c7337

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_geometricallyConnected_of_isPullback_of_surjective
import Theorems.Thm_GlobalTheory_isAffineHom_of_flatQuotient_of_affine_kernel
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_splitTorus_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] (E : TorusExtension G) : Smooth E.q.left ∧ GeometricallyConnected E.q.left ∧ Smooth G.hom ∧ GeometricallyConnected G.hom ∧ IsSeparated G.hom := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_flat
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI : Smooth E.B.hom := E.isAbelian.smooth
  haveI : GeometricallyConnected E.B.hom := E.isAbelian.geomConnected
  haveI : IsProper E.B.hom := E.isAbelian.proper
  have hTc : GeometricallyConnected (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    ((GlobalTheory.splitTorus_properties (Spec (CommRingCat.of K))).1 E.X).2.2.2.2.2.2.2.1
  have hiq : E.i ≫ E.q = 1 := E.isKernel.w
  have key : ∀ {W : Over (Spec (CommRingCat.of K))} (a b : W ⟶ G), a ≫ E.q = b ≫ E.q →
      (a⁻¹ * b) ≫ E.q = toUnit W ≫ (η : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.B) := by
    intro W a b hab
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, _root_.inv_mul_cancel]
    try exact rfl
  let m : G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X ⟶ G := fst _ _ * (snd _ _ ≫ E.i)
  have hm : ∀ {W : Over (Spec (CommRingCat.of K))} (l : W ⟶ G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X),
      l ≫ m = (l ≫ fst _ _) * ((l ≫ snd _ _) ≫ E.i) := by
    intro W l
    simp only [m, MonObj.comp_mul, Category.assoc]
  have hw : fst _ _ ≫ E.q = m ≫ E.q := by
    simp only [m, MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  have hsq : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)) m E.q E.q :=
    IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
      (fun c => lift c.fst (E.isKernel.lift (c.fst⁻¹ * c.snd) (toUnit _) (key _ _ c.condition)))
      (fun c => by rw [lift_fst])
      (fun c => by rw [hm, lift_fst, lift_snd, IsPullback.lift_fst, mul_inv_cancel_left])
      (fun c l h1 h2 => by
        refine CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, h1]) ?_
        rw [lift_snd]
        refine E.isKernel.hom_ext ?_ (toUnit_unique _ _)
        rw [IsPullback.lift_fst]
        rw [hm, h1] at h2
        exact eq_inv_mul_of_mul_eq h2))
  have hsqS : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left m.left
      E.q.left E.q.left := hsq.map (Over.forget _)
  have hprod : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left
      (snd G (splitTorus (Spec (CommRingCat.of K)) E.X)).left G.hom
      (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    IsPullback.of_hasPullback _ _
  have hfs : Smooth (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hprod.flip inferInstance
  have hfc : GeometricallyConnected (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprod.flip hTc
  have hqs : Smooth E.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsqS
      ⟨⟨E.q_surjective, E.q_flat⟩, E.q_quasiCompact⟩ hfs
  have hqc : GeometricallyConnected E.q.left :=
    GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hsqS.flip
  have hqa : IsAffineHom E.q.left :=
    GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel _ G E.B _ E.q E.i E.q_hom E.i_hom
      E.q_flat E.q_surjective E.q_quasiCompact E.isKernel inferInstance
  rw [← Over.w E.q]
  refine ⟨hqs, hqc, inferInstance, GeometricallyConnected.comp _ _, inferInstance⟩
end GlobalTheory
