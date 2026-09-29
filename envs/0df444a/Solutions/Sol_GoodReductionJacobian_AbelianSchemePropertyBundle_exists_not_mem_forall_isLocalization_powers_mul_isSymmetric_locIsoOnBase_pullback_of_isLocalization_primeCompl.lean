-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5884d16d-a3b8-51f3-bb7d-24328c4122de

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_not_mem_forall_isUnit_locIsoOnBase_pullback_of_locIsoOnBase_isLocalization_primeCompl
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace LSC22

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

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

structure StagePair (X Y : Type) [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y] where
  φ : X →+* Y
  hφ : φ.comp (algebraMap S X) = algebraMap S Y
  LX : RelativeGroupLaw X (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
  hLX : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X)) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))),
    (LX.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) =
      (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
        ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1
  LY : RelativeGroupLaw Y (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
  hLY : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Y)) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))),
    (LY.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) =
      (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S Y)))
        ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1
  ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))
  hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))
  hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom φ)

namespace StagePair

variable {L} {X Y : Type} [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y] (D : StagePair L X Y)

theorem comm_negMor : D.ρ ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) D.LX = negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) D.LY ≫ D.ρ :=
  GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible L X Y D.φ D.hφ D.LX D.LY D.hLX D.hLY
    D.ρ D.hρ₁ D.hρ₂

noncomputable def isoNeg (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules) :
    (Scheme.Modules.pullback D.ρ).obj ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) D.LX)).obj 𝓜) ≅
      (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) D.LY)).obj ((Scheme.Modules.pullback D.ρ).obj 𝓜) :=
  (Scheme.Modules.pullbackComp D.ρ _).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr D.comm_negMor).app 𝓜 ≪≫
    ((Scheme.Modules.pullbackComp _ D.ρ).app 𝓜).symm

noncomputable def isoFst (𝓛 : A.Modules) :
    (Scheme.Modules.pullback D.ρ).obj ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))))).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))).obj 𝓛 :=
  (Scheme.Modules.pullbackComp D.ρ _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr D.hρ₁).app 𝓛

noncomputable def isoSq (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules) :
    (Scheme.Modules.pullback D.ρ).obj (𝓜 ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) D.LX)).obj 𝓜) ≅
      (Scheme.Modules.pullback D.ρ).obj 𝓜 ⊗
        (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) D.LY)).obj ((Scheme.Modules.pullback D.ρ).obj 𝓜) :=
  Scheme.Modules.pullbackTensorObjIso D.ρ _ _ ≪≫ whiskerLeftIso _ (D.isoNeg 𝓜)

end StagePair

end LSC22

open LSC22 in

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (g₁ : S) (hg₁ : g₁ ∉ 𝔭.asIdeal)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g₁) C] [IsScalarTower S (Localization.Away g₁) C]
    (hCfin : Module.Finite (Localization.Away g₁) C)
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra C C₀] [IsScalarTower S C C₀]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀]
    (r : S) (hr : r ∉ 𝔭.asIdeal)
    (X : Type) [CommRing X] [Algebra S X] [Algebra C X] [IsScalarTower S C X]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) X]
    (LX : RelativeGroupLaw X (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))))
    (hLX : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))),
        (LX.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (φ : X →+* C₀) (hφ : φ.comp (algebraMap C X) = algebraMap C C₀)
    (κ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
    (hκ₁ : κ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
    (hκ₂ : κ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ≫ Spec.map (CommRingCat.ofHom φ))
    (L₀ : RelativeGroupLaw C₀ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))))
    (hL₀ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C₀))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C₀)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (hsym : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀ ((Scheme.Modules.pullback κ).obj 𝓜))
    (hsq : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
      ((Scheme.Modules.pullback κ).obj 𝓜 ⊗
        (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀)).obj ((Scheme.Modules.pullback κ).obj 𝓜))) :
    ∃ r' : S, r' ∉ 𝔭.asIdeal ∧
      ∀ (Y : Type) [CommRing Y] [Algebra S Y] [Algebra C Y] [IsScalarTower S C Y]
        [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers (r * r'))) Y]
        (ψ : X →+* Y) (_ : ψ.comp (algebraMap C X) = algebraMap C Y)
        (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
        (_ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
        (_ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom ψ))
        (LY : RelativeGroupLaw Y (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))))
    (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Y))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))),
        (LY.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S Y)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)),
        IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY ((Scheme.Modules.pullback ρ).obj 𝓜) ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))).obj 𝓛)
          ((Scheme.Modules.pullback ρ).obj 𝓜 ⊗
            (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY)).obj ((Scheme.Modules.pullback ρ).obj 𝓜)) := by
  classical

  let D₀ : StagePair L X C₀ := ⟨φ, by rw [IsScalarTower.algebraMap_eq S C X, ← RingHom.comp_assoc, hφ, ← IsScalarTower.algebraMap_eq], LX, hLX, L₀, hL₀, κ, hκ₁, hκ₂⟩

  have h₁ : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
      ((Scheme.Modules.pullback κ).obj ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX)).obj 𝓜))
      ((Scheme.Modules.pullback κ).obj 𝓜) :=
    locIsoOnBase_of_iso_left _ (D₀.isoNeg 𝓜) hsym
  obtain ⟨r₁, hr₁, H₁⟩ :=
    AlgebraicGeometry.Polarisation.exists_not_mem_forall_isUnit_locIsoOnBase_pullback_of_locIsoOnBase_isLocalization_primeCompl
      hA 𝔭 g₁ hg₁ C hCfin C₀ r hr X _ _ ((h𝓜.pullback _)) h𝓜 φ hφ κ hκ₁ hκ₂ h₁

  have h₂ : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
      ((Scheme.Modules.pullback κ).obj ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))))).obj 𝓛))
      ((Scheme.Modules.pullback κ).obj (𝓜 ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX)).obj 𝓜)) :=
    locIsoOnBase_of_iso_right _ (D₀.isoSq 𝓜).symm (locIsoOnBase_of_iso_left _ (D₀.isoFst 𝓛) hsq)
  obtain ⟨r₂, hr₂, H₂⟩ :=
    AlgebraicGeometry.Polarisation.exists_not_mem_forall_isUnit_locIsoOnBase_pullback_of_locIsoOnBase_isLocalization_primeCompl
      hA 𝔭 g₁ hg₁ C hCfin C₀ r hr X _ _ (h𝓛.pullback _)
      (AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓜 (h𝓜.pullback _)) φ hφ κ hκ₁ hκ₂ h₂
  refine ⟨r₁ * r₂, fun h => (𝔭.isPrime.mem_or_mem h).elim hr₁ hr₂, ?_⟩
  intro Y _ _ _ _ _ ψ hψ ρ hρ₁ hρ₂ LY hLY

  have hu : IsUnit (algebraMap S Y (r * (r₁ * r₂))) := by
    rw [IsScalarTower.algebraMap_apply S C Y]
    exact IsLocalization.map_units (M := Algebra.algebraMapSubmonoid C (Submonoid.powers (r * (r₁ * r₂)))) Y
      ⟨algebraMap S C (r * (r₁ * r₂)), Algebra.mem_algebraMapSubmonoid_of_mem ⟨r * (r₁ * r₂), Submonoid.mem_powers _⟩⟩
  have hu₁ : IsUnit (algebraMap S Y (r * r₁)) := by
    rw [← mul_assoc, map_mul] at hu; exact isUnit_of_mul_isUnit_left hu
  have hu₂ : IsUnit (algebraMap S Y (r * r₂)) := by
    rw [mul_left_comm, map_mul] at hu; exact isUnit_of_mul_isUnit_right hu
  let D : StagePair L X Y := ⟨ψ, by rw [IsScalarTower.algebraMap_eq S C X, ← RingHom.comp_assoc, hψ, ← IsScalarTower.algebraMap_eq], LX, hLX, LY, hLY, ρ, hρ₁, hρ₂⟩
  refine ⟨?_, ?_⟩
  · exact locIsoOnBase_of_iso_left _ (D.isoNeg 𝓜).symm (H₁ Y hu₁ ψ hψ ρ hρ₁ hρ₂)
  · exact locIsoOnBase_of_iso_right _ (D.isoSq 𝓜)
      (locIsoOnBase_of_iso_left _ (D.isoFst 𝓛).symm (H₂ Y hu₂ ψ hψ ρ hρ₁ hρ₂))

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl (solution)
