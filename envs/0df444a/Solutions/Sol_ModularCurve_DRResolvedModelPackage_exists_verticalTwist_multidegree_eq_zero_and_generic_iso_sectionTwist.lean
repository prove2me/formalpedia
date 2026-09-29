-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/c3be0236-1234-534e-afa6-f9b0c77a6c1a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit

import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

open AlgebraicGeometry.RelPicard

universe u

namespace K4MON

noncomputable def foldrTensorIso {C : Type*} [Category C] [MonoidalCategory C] {ι : Type*} (A B : ι → C) (V : C) :
    ∀ l : List ι, l.foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ C)) ⊗ V
  | [] => (λ_ V).symm
  | j :: l => whiskerLeftIso (A j) (whiskerLeftIso (B j) (foldrTensorIso A B V l)) ≪≫
      (α_ (A j) (B j) _).symm ≪≫ (α_ (A j ⊗ B j) _ V).symm

theorem foldr_tensor_iso_foldr_tensorUnit_tensor {C : Type*} [Category C] [MonoidalCategory C] {ι : Type*}
    (A B : ι → C) (V : C) (l : List ι) :
    Nonempty (l.foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ C)) ⊗ V) :=
  ⟨foldrTensorIso A B V l⟩

noncomputable def pullbackFoldrIso {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (A B : ι → Y.Modules) (A' B' : ι → X.Modules)
    (eA : ∀ j, (Scheme.Modules.pullback f).obj (A j) ≅ A' j) (eB : ∀ j, (Scheme.Modules.pullback f).obj (B j) ≅ B' j) :
    ∀ l : List ι, (Scheme.Modules.pullback f).obj (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)) ≅
      l.foldr (fun j M => (A' j ⊗ B' j) ⊗ M) (𝟙_ X.Modules)
  | [] => Scheme.Modules.pullbackTensorUnitObjIso f
  | j :: l => Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
      tensorIso (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ tensorIso (eA j) (eB j)) (pullbackFoldrIso f A B A' B' eA eB l)

theorem nonempty_pullback_foldr_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (A B : ι → Y.Modules) (A' B' : ι → X.Modules)
    (eA : ∀ j, (Scheme.Modules.pullback f).obj (A j) ≅ A' j) (eB : ∀ j, (Scheme.Modules.pullback f).obj (B j) ≅ B' j) (l : List ι) :
    Nonempty ((Scheme.Modules.pullback f).obj (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)) ≅
      l.foldr (fun j M => (A' j ⊗ B' j) ⊗ M) (𝟙_ X.Modules)) :=
  ⟨pullbackFoldrIso f A B A' B' eA eB l⟩

end K4MON

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top Scheme.Modules.pullback Scheme.Hom Spec Spec.map Scheme Scheme.IdealSheafData.support_top IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.isInvertible_top Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf IdealSheafData.one_eq_top Modules.pullback Hom IdealSheafData.support_top basicOpen Modules.pullbackCongr IdealSheafData.support_mul Modules Opens Hom.comp_apply IdealSheafData Modules.pullbackComp Modules.IsInvertible Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso IdealSheafData.isInvertible_top Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "app injective continuous ker comp_apply nonempty_pullback_ker_pow_invModule_iso_of_isIso isInvertible_ker_of_comp_eq_id_of_mem_opens" end AlgebraicGeometry.Scheme.Hom
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in
theorem AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem' {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage PlaceSpecialization DRResolvedModelPackage X0MqComponents x0MqResolvedTable"
namespace K4
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry.Scheme"

theorem toNat_neg_sub_toNat (n : ℤ) : (((-n).toNat : ℕ) : ℤ) - ((n.toNat : ℕ) : ℤ) = -n := by
  have h := Int.toNat_sub_toNat_neg (-n)
  rw [neg_neg] at h
  exact h

theorem exists_twist_of_mem_range {ι : Type*} (α : (ι → ℤ) →+ (ι → ℤ)) (h : ι → ℤ) (hh : h ∈ α.range) :
    ∃ (aplus aminus : ι → ℕ), ∀ c, h c + α (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c = 0 := by
  obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp hh
  refine ⟨fun F => (-(b F)).toNat, fun F => (b F).toNat, fun c => ?_⟩
  have hfun : (fun F => (((-(b F)).toNat : ℕ) : ℤ) - (((b F).toNat : ℕ) : ℤ)) = -b := by
    funext F; rw [toNat_neg_sub_toNat]; rfl
  rw [hfun, map_neg, ← hb, Pi.neg_apply, add_neg_cancel]

theorem isInvertible_prod_pow {X : Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι] (I : ι → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (n : ι → ℕ) : (∏ i, I i ^ n i).IsInvertible := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  · intro i s hi ih
    rw [Finset.prod_insert hi]
    exact ((hI i).pow (n i)).mul ih

theorem isInvertible_foldr {X : Scheme.{u}} {m : ℕ} (A B : Fin m → X.Modules)
    (hA : ∀ j, Scheme.Modules.IsInvertible (A j)) (hB : ∀ j, Scheme.Modules.IsInvertible (B j))
    (V : X.Modules) (hV : Scheme.Modules.IsInvertible V) (l : List (Fin m)) :
    Scheme.Modules.IsInvertible (l.foldr (fun j N => A j ⊗ B j ⊗ N) V) := by
  induction l with
  | nil => exact hV
  | cons j l ih => exact (hA j).tensor ((hB j).tensor ih)

end ModularCurve.K4

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage PlaceSpecialization DRResolvedModelPackage X0MqComponents x0MqResolvedTable"
namespace K4
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry.Scheme"

theorem support_pow_le {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) : (I ^ n).support ≤ I.support := by
  induction n with
  | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]; exact bot_le
  | succ n ih =>
    rw [pow_succ, Scheme.IdealSheafData.support_mul]
    exact sup_le ih le_rfl

theorem not_mem_support_top {X : Scheme.{u}} (x : X) : x ∉ (⊤ : X.IdealSheafData).support := by
  rw [Scheme.IdealSheafData.support_top]
  show x ∉ ((⊥ : TopologicalSpace.Closeds X) : Set X)
  rw [TopologicalSpace.Closeds.coe_bot]; exact Set.notMem_empty x

theorem mem_support_prod_pow {X : Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι] (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (x : X) (hx : x ∈ (∏ i, I i ^ n i).support) : ∃ i, x ∈ (I i).support := by
  classical
  have key : ∀ s : Finset ι, x ∈ (∏ i ∈ s, I i ^ n i).support → ∃ i, x ∈ (I i).support := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro h
      rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top] at h
      exact absurd h (not_mem_support_top x)
    · intro i s hi ih h
      rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul] at h
      rcases h with h | h
      · exact ⟨i, support_pow_le (I i) (n i) h⟩
      · exact ih h
  exact key Finset.univ hx

end ModularCurve.K4

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage PlaceSpecialization DRResolvedModelPackage X0MqComponents x0MqResolvedTable"
namespace K4
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry.Scheme"

theorem nonempty_pullback_invModule_tensor_module_iso_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J N : X.IdealSheafData) (hJ : J.IsInvertible) (hN : N.IsInvertible)
    (hJs : ∀ y : Y, f.base y ∉ (J.support : Set X)) (hNs : ∀ y : Y, f.base y ∉ (N.support : Set X)) :
    Nonempty ((Scheme.Modules.pullback f).obj (J.invModule ⊗ N.module) ≅ 𝟙_ Y.Modules) := by
  obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support f J hJ
    N hN 1 hJs hNs (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟨Iso.refl _⟩
  let iJ : J.invModule ≅ (J ^ 1).invModule := eqToIso (by rw [pow_one])
  let i1 : J.invModule ⊗ N.module ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⊗ ((J ^ 1).invModule ⊗ N.module) :=
    (λ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorIso iJ (Iso.refl _))
  exact ⟨(Scheme.Modules.pullback f).mapIso i1 ≪≫ e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f⟩

theorem specMap_base_mem_basicOpen {O K : Type u} [CommRing O] [Field K] (φ : O →+* K) (r : O) (hr : φ r ≠ 0)
    (q : Spec (CommRingCat.of K)) :
    (Spec.map (CommRingCat.ofHom φ)).base q ∈ PrimeSpectrum.basicOpen r := by
  have h1 : ((Spec.map (CommRingCat.ofHom φ)).base q).asIdeal = Ideal.comap φ q.asIdeal := rfl
  have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  show r ∉ ((Spec.map (CommRingCat.ofHom φ)).base q).asIdeal
  rw [h1, Ideal.mem_comap, hq, Ideal.mem_bot]
  exact hr

end ModularCurve.K4

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage PlaceSpecialization DRResolvedModelPackage X0MqComponents x0MqResolvedTable"
namespace K4
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist.AlgebraicGeometry.Scheme AlgebraicGeometry.RelPicard"

theorem isClosedImmersion_of_comp_eq_id' {Y S : Scheme.{u}} (π : Y ⟶ S) [IsSeparated π] (σ : S ⟶ Y) (hσ : σ ≫ π = 𝟙 _) :
    IsClosedImmersion σ := by
  have : IsClosedImmersion (σ ≫ π) := by rw [hσ]; infer_instance
  exact .of_comp σ π

set_option maxHeartbeats 6400000 in

theorem nonempty_generic_iso
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Y : Scheme.{0}} (c : Y ⟶ Spec (CommRingCat.of O)) [IsSeparated c]
    (U : Y.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) c) (pos neg : Fin m → ℕ)
    (hσU : ∀ j, Set.range (σ j).1 ⊆ (U : Set Y))
    (hker : ∀ j, ((σ j).1).ker.IsInvertible)
    (V : Y.Modules)
    (hV : Nonempty ((Scheme.Modules.pullback (pullback.fst c
        (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj V ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst c
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj
            ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N) V) ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist c (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal c (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback c (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)) := by
  classical

  let t' : Spec (CommRingCat.of (FractionRing O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))
  let jη := pullback.fst c t'
  let fst₁ := pullback.fst c (𝟙 (Spec (CommRingCat.of O)))
  haveI : IsIso fst₁ := inferInstance
  let ψ : SchemeHomOver t' (𝟙 (Spec (CommRingCat.of O))) := ⟨t', Category.comp_id _⟩
  have hcomp : baseChangeSnd c ψ ≫ fst₁ = jη := by
    simp only [baseChangeSnd, fst₁, jη, pullback.lift_fst, Category.comp_id]
  let A : Fin m → Y.Modules := fun j => ((σ j).1.ker ^ (pos j)).invModule
  let B : Fin m → Y.Modules := fun j => ((σ j).1.ker ^ (neg j)).module
  let A₁ : Fin m → (pullback c (𝟙 (Spec (CommRingCat.of O)))).Modules := fun j =>
    sectionTwist c (σ j) (𝟙 _) (pos j)
  let B₁ : Fin m → (pullback c (𝟙 (Spec (CommRingCat.of O)))).Modules := fun j =>
    ((sectionIdeal c (σ j) (𝟙 _)) ^ (neg j)).module

  have hsec : ∀ j, (sectionIdeal c (σ j) (𝟙 (Spec (CommRingCat.of O)))).IsInvertible := fun j =>
    isInvertible_sectionIdeal_of_range_subset c (σ j) U (hσU j) (𝟙 _)
  haveI : ∀ j, IsClosedImmersion (σ j).1 := fun j => isClosedImmersion_of_comp_eq_id' c (σ j).1 (σ j).2
  have hrig : ∀ j, rigSection c (𝟙 (Spec (CommRingCat.of O))) (σ j) ≫ fst₁ = (σ j).1 := fun j => by
    show pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst, Category.id_comp]
  have eAB := fun j => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso fst₁ (σ j).1
    (rigSection c (𝟙 _) (σ j)) (hrig j) (hker j) (hsec j)
  let eA : ∀ j, (Scheme.Modules.pullback fst₁).obj (A j) ≅ A₁ j := fun j => ((eAB j (pos j)).1).some
  let eB : ∀ j, (Scheme.Modules.pullback fst₁).obj (B j) ≅ B₁ j := fun j => ((eAB j (neg j)).2).some

  let S'' : Y.Modules := (List.finRange m).foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)
  let i0 : (List.finRange m).foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ S'' ⊗ V := K4MON.foldrTensorIso A B V _
  let i1 : (Scheme.Modules.pullback jη).obj (S'' ⊗ V) ≅
      (Scheme.Modules.pullback jη).obj S'' ⊗ (Scheme.Modules.pullback jη).obj V := Scheme.Modules.pullbackTensorObjIso jη _ _
  let i2 : (Scheme.Modules.pullback jη).obj S'' ⊗ (Scheme.Modules.pullback jη).obj V ≅
      (Scheme.Modules.pullback jη).obj S'' := tensorIso (Iso.refl _) hV.some ≪≫ ρ_ _
  let i3 : (Scheme.Modules.pullback jη).obj S'' ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback fst₁).obj S'') :=
    ((Scheme.Modules.pullbackCongr hcomp).symm ≪≫ (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) fst₁).symm).app S''
  let i4 : (Scheme.Modules.pullback fst₁).obj S'' ≅
      (List.finRange m).foldr (fun j M => (A₁ j ⊗ B₁ j) ⊗ M) (𝟙_ _) := K4MON.pullbackFoldrIso fst₁ A B A₁ B₁ eA eB _
  obtain ⟨-, ⟨i5⟩⟩ := isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset c U σ hσU pos neg ψ
  exact ⟨(Scheme.Modules.pullback jη).mapIso i0 ≪≫ i1 ≪≫ i2 ≪≫ i3 ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso i4 ≪≫ i5⟩

end ModularCurve.K4

open ModularCurve.K4 in
set_option maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (hrange : (fun w : X0MqComponents 𝔛reg.width => (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) w) ∈
        (MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)).range) :
    ∃ (aplus aminus : X0MqComponents 𝔛reg.width → ℕ),

      (∀ c : X0MqComponents 𝔛reg.width,
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) c +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c = 0) ∧
      Scheme.Modules.IsInvertible ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)) ∧
      Nonempty ((Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj
            ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)) ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)) := by
  classical

  obtain ⟨aplus, aminus, hdeg0⟩ := exists_twist_of_mem_range
    (MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width))
    (fun w => (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) w) hrange
  refine ⟨aplus, aminus, hdeg0, ?_, ?_⟩
  ·
    have hker : ∀ j, ((σ j).1).ker.IsInvertible := fun j =>
      AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges
        (σ j).1 (σ j).2 (hv j).1
    refine isInvertible_foldr _ _ (fun j => ((hker j).pow (pos j)).isInvertible_invModule)
      (fun j => ((hker j).pow (neg j)).isInvertible_module) _ ?_ (List.finRange m)
    exact (isInvertible_prod_pow _ 𝔛reg.comp_isInvertible aplus).isInvertible_invModule.tensor
      (isInvertible_prod_pow _ 𝔛reg.comp_isInvertible aminus).isInvertible_module
  ·
    have hker : ∀ j, ((σ j).1).ker.IsInvertible := fun j =>
      AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges
        (σ j).1 (σ j).2 (hv j).1
    have hσU : ∀ j, Set.range (σ j).1 ⊆ (𝔛reg.smoothOffEdges : Set 𝔛reg.Y) := fun j =>
      AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem' 𝔛reg.smoothOffEdges (σ j).1 (hv j).1

    have hp0 : ((p : ℕ) : O) ≠ 0 := fun h => by
      apply IsDiscreteValuationRing.not_a_field O
      rw [hϖ, h, Ideal.span_singleton_eq_bot]
    have hpK : algebraMap O (FractionRing O) ((p : ℕ) : O) ≠ 0 := fun h =>
      hp0 ((IsFractionRing.injective O (FractionRing O)) (by rw [h, map_zero]))
    have hgen : ∀ y : ↥(pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))),
        (pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))).base y ∈
          𝔛reg.toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
      intro y
      show (pullback.fst _ _ ≫ 𝔛reg.toBase).base y ∈ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
      rw [pullback.condition, Scheme.Hom.comp_apply]
      exact specMap_base_mem_basicOpen (algebraMap O (FractionRing O)) _ hpK _
    have hVs : ∀ (n : X0MqComponents 𝔛reg.width → ℕ)
        (y : ↥(pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))),
        (pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))).base y ∉
          ((∏ F, 𝔛reg.comp F ^ n F).support : Set 𝔛reg.Y) := by
      intro n y hy
      obtain ⟨F, hF⟩ := mem_support_prod_pow _ n _ hy
      exact 𝔛reg.comp_support F _ hF (hgen y)
    have hV := nonempty_pullback_invModule_tensor_module_iso_unit
      (pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))
      (∏ F, 𝔛reg.comp F ^ aplus F) (∏ F, 𝔛reg.comp F ^ aminus F)
      (isInvertible_prod_pow _ 𝔛reg.comp_isInvertible aplus) (isInvertible_prod_pow _ 𝔛reg.comp_isInvertible aminus)
      (hVs aplus) (hVs aminus)
    exact nonempty_generic_iso 𝔛reg.toBase 𝔛reg.smoothOffEdges σ pos neg hσU hker _ hV

end S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_exists_verticalTwist_multidegree_eq_zero_and_generic_iso_sectionTwist (solution)
