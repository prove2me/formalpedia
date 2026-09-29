-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isLocalization_powers_exists_isSymmetric_locIsoOnBase_iso_of_isLocalization_primeCompl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d464b227-e3b7-5b52-804d-67c62c3c73a7

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_exists_isInvertible_pullback_iso_of_isLocalization_primeCompl
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_exists_isSymmetric_locIsoOnBase_iso_of_isLocalization_primeCompl
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace LSQ22

open GoodReductionJacobian.RelativeGroupLaw

theorem locIsoOnBase_of_iso_left {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N N' P : X.Modules} (e : N ≅ N') (h : LocIsoOnBase g N' P) : LocIsoOnBase g N P := by
  intro s
  obtain ⟨U, hs, ⟨φ⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ φ⟩⟩

theorem locIsoOnBase_of_iso_right {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N P P' : X.Modules} (e : P ≅ P') (h : LocIsoOnBase g N P) : LocIsoOnBase g N P' := by
  intro s
  obtain ⟨U, hs, ⟨φ⟩⟩ := h s
  exact ⟨U, hs, ⟨φ ≪≫ (Scheme.Modules.pullback _).mapIso e⟩⟩

end LSQ22

open LSQ22 GoodReductionJacobian.RelativeGroupLaw in

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (g₁ : S) (hg₁ : g₁ ∉ 𝔭.asIdeal)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g₁) C] [IsScalarTower S (Localization.Away g₁) C]
    (hCfin : Module.Finite (Localization.Away g₁) C)
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra C C₀] [IsScalarTower S C C₀]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀]
    (L₀ : RelativeGroupLaw C₀ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))))
    (hL₀ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C₀))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C₀)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))).Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hsym : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀ 𝓛₀)
    (hsq : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
      (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀)).obj 𝓛₀)) :
    ∃ r₁ : S, r₁ ∉ 𝔭.asIdeal ∧
      ∀ (C₁ : Type) [CommRing C₁] [Algebra S C₁] [Algebra C C₁] [IsScalarTower S C C₁]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r₁)) C₁]
        (φ₀ : C₁ →+* C₀) (_ : φ₀.comp (algebraMap C C₁) = algebraMap C C₀)
        (ρ₀ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))))
    (_ : ρ₀ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
    (_ : ρ₀ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ≫ Spec.map (CommRingCat.ofHom φ₀))
        (L₁ : RelativeGroupLaw C₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁)))))
        (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C₁))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C₁)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)),
        ∃ 𝓛₁ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₁)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₁ ∧
          IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁)))) L₁ 𝓛₁ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))))).obj 𝓛)
            (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁)))) L₁)).obj 𝓛₁) ∧
          Nonempty ((Scheme.Modules.pullback ρ₀).obj 𝓛₁ ≅ 𝓛₀) := by
  classical
  haveI : Module.Finite (Localization.Away g₁) C := hCfin

  obtain ⟨r, hr, HAB⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isUnit_exists_isInvertible_pullback_iso_of_isLocalization_primeCompl
      hA 𝔭 C C₀ 𝓛₀ h𝓛₀

  let M : Submonoid C := Algebra.algebraMapSubmonoid C (Submonoid.powers r)
  let X : Type := Localization M
  have hMunit₀ : ∀ y : M, IsUnit (algebraMap C C₀ y) := by
    rintro ⟨y, hy⟩
    obtain ⟨s, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_map.1 hy
    refine IsLocalization.map_units (M := Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀
      ⟨algebraMap S C (r ^ n), Algebra.mem_algebraMapSubmonoid_of_mem ⟨r ^ n, ?_⟩⟩
    exact fun h => hr (𝔭.isPrime.mem_of_pow_mem n h)
  let φX : X →+* C₀ := IsLocalization.lift hMunit₀
  have hφX : φX.comp (algebraMap C X) = algebraMap C C₀ := IsLocalization.lift_comp hMunit₀
  have hrX : IsUnit (algebraMap S X r) := by
    rw [IsScalarTower.algebraMap_apply S C X]
    exact IsLocalization.map_units X ⟨algebraMap S C r, Algebra.mem_algebraMapSubmonoid_of_mem ⟨r, Submonoid.mem_powers r⟩⟩
  have hSpecφX : Spec.map (CommRingCat.ofHom φX) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S C₀)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq S C X, ← RingHom.comp_assoc, hφX,
      ← IsScalarTower.algebraMap_eq]
  let κ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φX))
      (by rw [Category.assoc, hSpecφX]; exact pullback.condition)
  have hκ₁ : κ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hκ₂ : κ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φX) := pullback.lift_snd _ _ _
  obtain ⟨𝓜X, h𝓜X, ⟨eX⟩⟩ := HAB X hrX φX hφX κ hκ₁ hκ₂

  let LX := L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S X)))
  have hLX : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X))
      (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))),
      (LX.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
          ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
            by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
            by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
    fun T t' P Q => congrArg Subtype.val (baseChangePointToBase_mul _ L t' P Q)
  have hsym' : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀
      ((Scheme.Modules.pullback κ).obj 𝓜X) :=
    locIsoOnBase_of_iso_right _ eX.symm
      (locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback _).mapIso eX) hsym)
  have hsq' : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
      ((Scheme.Modules.pullback κ).obj 𝓜X ⊗
        (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀)).obj
          ((Scheme.Modules.pullback κ).obj 𝓜X)) :=
    locIsoOnBase_of_iso_right _ (eX.symm ⊗ᵢ (Scheme.Modules.pullback _).mapIso eX.symm) hsq

  obtain ⟨r', hr', HC⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
      L hA 𝓛 h𝓛 𝔭 g₁ hg₁ C hCfin C₀ r hr X LX hLX 𝓜X h𝓜X φX hφX κ hκ₁ hκ₂ L₀ hL₀ hsym' hsq'
  refine ⟨r * r', fun h => (𝔭.isPrime.mem_or_mem h).elim hr hr', ?_⟩
  intro C₁ _ _ _ _ _ φ₀ hφ₀ ρ₀ hρ₀₁ hρ₀₂ L₁ hL₁

  have hMunit₁ : ∀ y : M, IsUnit (algebraMap C C₁ y) := by
    rintro ⟨y, hy⟩
    obtain ⟨s, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_map.1 hy
    have h1 : IsUnit (algebraMap C C₁ (algebraMap S C (r * r'))) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid C (Submonoid.powers (r * r'))) C₁
        ⟨algebraMap S C (r * r'), Algebra.mem_algebraMapSubmonoid_of_mem ⟨r * r', Submonoid.mem_powers _⟩⟩
    have h2 : IsUnit (algebraMap C C₁ (algebraMap S C r)) := by
      rw [map_mul, map_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    show IsUnit (algebraMap C C₁ (algebraMap S C (r ^ n)))
    rw [map_pow, map_pow]
    exact h2.pow n
  let ψ : X →+* C₁ := IsLocalization.lift hMunit₁
  have hψ : ψ.comp (algebraMap C X) = algebraMap C C₁ := IsLocalization.lift_comp hMunit₁
  have hSpecψ : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)) =
      Spec.map (CommRingCat.ofHom (algebraMap S C₁)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq S C X, ← RingHom.comp_assoc, hψ,
      ← IsScalarTower.algebraMap_eq]
  let ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [Category.assoc, hSpecψ]; exact pullback.condition)
  have hρ₁ : ρ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hρ₂ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
  obtain ⟨hsymY, hsqY⟩ := HC C₁ ψ hψ ρ hρ₁ hρ₂ L₁ hL₁
  refine ⟨(Scheme.Modules.pullback ρ).obj 𝓜X, h𝓜X.pullback ρ, hsymY, hsqY, ⟨?_⟩⟩

  have hφψ : φ₀.comp ψ = φX :=
    IsLocalization.ringHom_ext M (by rw [RingHom.comp_assoc, hψ, hφ₀, hφX])
  have hcomp : ρ₀ ≫ ρ = κ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hρ₁, hρ₀₁, hκ₁]
    · rw [Category.assoc, hρ₂, ← Category.assoc, hρ₀₂, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφψ, hκ₂]
  exact (Scheme.Modules.pullbackComp ρ₀ ρ).app 𝓜X ≪≫ (Scheme.Modules.pullbackCongr hcomp).app 𝓜X ≪≫ eX

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_exists_isSymmetric_locIsoOnBase_iso_of_isLocalization_primeCompl
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_exists_isSymmetric_locIsoOnBase_iso_of_isLocalization_primeCompl (solution)
