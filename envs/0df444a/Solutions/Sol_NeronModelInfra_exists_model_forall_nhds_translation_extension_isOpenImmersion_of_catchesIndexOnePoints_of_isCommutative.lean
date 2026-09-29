-- Prove2me | solution 1 for NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4d6eb2b7-822a-5dde-982a-712aa4cc5080

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
import Theorems.Thm_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
import Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension
import Theorems.Thm_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK),
      Smooth f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      (∃ x : X, f.base x = IsLocalRing.closedPoint R) ∧ IsIso e.1 ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)).1) := by
  classical

  obtain ⟨d, hd⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth LXK
  obtain ⟨ω, hωframe, hleft⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq gK LXK d

  obtain ⟨D, hD⟩ :=
    NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints K LXK M hfin hM hpts d ω
      hωframe

  obtain ⟨X, g, eX, V, j, hsm, hsep, hlft, hqc, hiso, hyV, hVK, hjopen, hjchart, hcover⟩ :=
    NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension K gK
      (fun c => (D.C c).Y) (fun c => (D.C c).f)
      (fun c => ⟨(D.C c).smooth, D.isSeparated c, (D.C c).locallyOfFiniteType, D.quasiCompact c⟩)
      (fun c => (D.C c).e) D.isIso (fun c => (D.C c).y) (fun c => (D.C c).hy) D.hgen D.inequiv

  obtain ⟨hL, hR⟩ :=
    NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
      K LXK hcomm M hM hpts d ω hωframe hleft D hD X g eX V j hyV hVK hjopen hjchart hcover
  obtain ⟨c₀⟩ := D.nonempty
  refine ⟨X, g, eX, hsm, hsep, hlft, hqc, ⟨(j c₀).1.base ⟨(D.C c₀).y, hyV c₀⟩, ?_⟩, hiso, hL, hR⟩

  have h2 := congrArg (fun φ => φ.base ⟨(D.C c₀).y, hyV c₀⟩) (j c₀).2
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
  exact h2.trans (D.C c₀).hy

end S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
end P2MW
export P2MW.S_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative (solution)
