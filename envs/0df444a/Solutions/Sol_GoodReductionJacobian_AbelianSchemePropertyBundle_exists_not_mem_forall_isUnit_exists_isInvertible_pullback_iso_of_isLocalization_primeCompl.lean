-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isUnit_exists_isInvertible_pullback_iso_of_isLocalization_primeCompl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fe9cb0cd-4dce-55d3-ac51-28300dd7df52

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_exists_isInvertible_pullback_iso_of_isLocalization_primeCompl
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace LP26

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}

abbrev bc (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

abbrev bcStr (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] :
    bc f X ⟶ Spec (CommRingCat.of X) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

abbrev bcFst (f : A ⟶ Spec (CommRingCat.of S)) (X : Type) [CommRing X] [Algebra S X] : bc f X ⟶ A :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X)))

theorem specMap_algebraMap_comp {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y] [Algebra X Y]
    [IsScalarTower S X Y] :
    Spec.map (CommRingCat.ofHom (algebraMap X Y)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S Y)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem isPullback_of_proj (f : A ⟶ Spec (CommRingCat.of S)) {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y]
    (ψ : X →+* Y)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S Y)))
    (φ : bc f Y ⟶ bc f X) (hφ₁ : φ ≫ bcFst f X = bcFst f Y) (hφ₂ : φ ≫ bcStr f X = bcStr f Y ≫ Spec.map (CommRingCat.ofHom ψ)) :
    IsPullback φ (bcStr f Y) (bcStr f X) (Spec.map (CommRingCat.ofHom ψ)) := by
  refine IsPullback.of_right ?_ hφ₂ (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
  rw [hφ₁, hψ]
  exact IsPullback.of_hasPullback f _

theorem exists_rho (f : A ⟶ Spec (CommRingCat.of S)) (X Y : Type) [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y]
    [Algebra X Y] [IsScalarTower S X Y] :
    ∃ ρ : bc f Y ⟶ bc f X, ρ ≫ bcFst f X = bcFst f Y ∧ ρ ≫ bcStr f X = bcStr f Y ≫ Spec.map (CommRingCat.ofHom (algebraMap X Y)) :=
  ⟨pullback.lift (bcFst f Y) (bcStr f Y ≫ Spec.map (CommRingCat.ofHom (algebraMap X Y)))
      (by rw [pullback.condition, Category.assoc, specMap_algebraMap_comp]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end LP26

open LP26 in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) (𝔭 : PrimeSpectrum S)
    (C : Type) [CommRing C] [Algebra S C]
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra C C₀] [IsScalarTower S C C₀]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀]
    (𝓜₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))).Modules) (h𝓜₀ : Scheme.Modules.IsInvertible 𝓜₀) :
    ∃ r : S, r ∉ 𝔭.asIdeal ∧
      ∀ (X : Type) [CommRing X] [Algebra S X] [Algebra C X] [IsScalarTower S C X] (_ : IsUnit (algebraMap S X r))
        (φ : X →+* C₀) (_ : φ.comp (algebraMap C X) = algebraMap C C₀)
        (κ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
        (_ : κ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
        (_ : κ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ≫ Spec.map (CommRingCat.ofHom φ)),
        ∃ 𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules,
          Scheme.Modules.IsInvertible 𝓜 ∧ Nonempty ((Scheme.Modules.pullback κ).obj 𝓜 ≅ 𝓜₀) := by
  classical
  haveI : IsProper f := hA.proper

  have hunits : ∀ y : 𝔭.asIdeal.primeCompl, IsUnit (algebraMap S C₀ y) := fun y => by
    rw [IsScalarTower.algebraMap_apply S C C₀]
    exact IsLocalization.map_units C₀ (⟨algebraMap S C y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ :
      Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl)
  obtain ⟨fm, hfmS⟩ : ∃ fm : Localization.AtPrime 𝔭.asIdeal →+* C₀,
      fm.comp (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) = algebraMap S C₀ :=
    ⟨IsLocalization.lift hunits, IsLocalization.lift_comp hunits⟩

  obtain ⟨ρ₀, hρ₀1, hρ₀2⟩ := exists_rho f C C₀
  have htop : IsPullback ρ₀ (bcStr f C₀) (bcStr f C) (Spec.map (CommRingCat.ofHom (algebraMap C C₀))) :=
    isPullback_of_proj f (algebraMap C C₀) specMap_algebraMap_comp ρ₀ hρ₀1 hρ₀2

  haveI : IsLocalization (𝔭.asIdeal.primeCompl.map (algebraMap S C)) C₀ :=
    ‹IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀›
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap C C₀))) (Spec.map (CommRingCat.ofHom fm))
      (Spec.map (CommRingCat.ofHom (algebraMap S C)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) :=
    AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isLocalization (algebraMap S C) fm
        (by rw [hfmS, IsScalarTower.algebraMap_eq S C C₀]) 𝔭.asIdeal.primeCompl)
  have hbig := htop.paste_vert hsq

  haveI : QuasiCompact (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C))) := inferInstance
  haveI : IsSeparated (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C))) := inferInstance
  obtain ⟨r, hr, ψ, hψ, 𝓛r, h𝓛r, ⟨ι⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_iso_pullback_of_isInvertible_atPrime_of_isSeparated
      (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C))) 𝔭.asIdeal
      ((Scheme.Modules.pullback hbig.isoPullback.inv).obj 𝓜₀) (h𝓜₀.pullback _)
  refine ⟨r, hr, fun X _ _ _ _ hu φ hφ κ hκ₁ hκ₂ => ?_⟩

  obtain ⟨τ, hτ⟩ : ∃ τ : Localization.Away r →+* X, τ.comp (algebraMap S (Localization.Away r)) = algebraMap S X :=
    ⟨IsLocalization.Away.lift r hu, IsLocalization.Away.lift_comp r hu⟩
  obtain ⟨ρX, hρX1, hρX2⟩ := exists_rho f C X
  have hθc : ρX ≫ (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C))) =
      (bcStr f X ≫ Spec.map (CommRingCat.ofHom τ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))) := by
    rw [← Category.assoc, hρX2]
    simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq S C X, hτ]
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : bc f X ⟶ pullback (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))),
      θ ≫ pullback.fst _ _ = ρX ∧ θ ≫ pullback.snd _ _ = bcStr f X ≫ Spec.map (CommRingCat.ofHom τ) :=
    ⟨pullback.lift _ _ hθc, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  refine ⟨(Scheme.Modules.pullback θ).obj 𝓛r, h𝓛r.pullback θ, ?_⟩

  have hring : φ.comp τ = fm.comp ψ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hτ, hψ, hfmS, IsScalarTower.algebraMap_eq S C X, ← RingHom.comp_assoc, hφ,
      ← IsScalarTower.algebraMap_eq S C C₀]
  have hκρ : κ ≫ ρX = ρ₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρX1, hρ₀1, hκ₁]
    · rw [Category.assoc, hρX2, hρ₀2, ← Category.assoc, hκ₂, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have hkey : κ ≫ θ = hbig.isoPullback.hom ≫
      pullback.lift
        (pullback.fst (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
          (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
        (pullback.snd (bcStr f C ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
          (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ Spec.map (CommRingCat.ofHom ψ))
        (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      exact hκρ
    · simp only [Category.assoc, hθ2, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc]
      rw [← Category.assoc, hκ₂, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, hring]
  exact ⟨(Scheme.Modules.pullbackComp κ θ).app 𝓛r ≪≫ (Scheme.Modules.pullbackCongr hkey).app 𝓛r ≪≫
    ((Scheme.Modules.pullbackComp hbig.isoPullback.hom _).app 𝓛r).symm ≪≫
    (Scheme.Modules.pullback hbig.isoPullback.hom).mapIso ι ≪≫
    (Scheme.Modules.pullbackComp hbig.isoPullback.hom hbig.isoPullback.inv).app 𝓜₀ ≪≫
    (Scheme.Modules.pullbackCongr hbig.isoPullback.hom_inv_id).app 𝓜₀ ≪≫
    (Scheme.Modules.pullbackId _).app 𝓜₀⟩

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_exists_isInvertible_pullback_iso_of_isLocalization_primeCompl
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_exists_isInvertible_pullback_iso_of_isLocalization_primeCompl (solution)
