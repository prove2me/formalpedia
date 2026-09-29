-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d830d7b9-dead-5bcf-b3e6-307d2a645290

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
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

open AlgebraicGeometry.RelPicard
open Opposite
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace K6aKit

theorem isIso_pullback_snd_of_isIso_morphismRestrict {X Y T : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)
    [hU : IsIso (g ∣_ U)] (h : T ⟶ X) (hh : Set.range h.base ⊆ (U : Set X)) : IsIso (pullback.snd g h) := by
  let h' : T ⟶ U := IsOpenImmersion.lift U.ι h (by rwa [Scheme.Opens.range_ι])
  have hh' : h' ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
  have sq := (IsPullback.of_hasPullback (g ∣_ U) h').paste_horiz (isPullback_morphismRestrict g U).flip
  rw [← hh', ← sq.isoPullback_inv_snd]
  infer_instance

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

theorem smooth_drModel_baseChange (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {K : Type} [CommRing K] (tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ))
    (s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of K))
    (hs : s ≫ tK = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) s) :
    SmoothOfRelativeDimension 1 (pullback.snd (DRModel.toBase p) tK) := by
  haveI := 𝔛.eη_iso
  let c := DRModel.toBase p
  let tQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))
  have hs' : s ≫ tK = tQ := hs
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd c tQ) :=
    smoothOfRelativeDimension_one_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη) (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])
  let e : pullback s (pullback.snd c tK) ≅ pullback c tQ :=
    pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso c tK s ≪≫ pullback.congrHom rfl hs'
  haveI : SmoothOfRelativeDimension 1 (pullback.fst s (pullback.snd c tK)) := by
    refine smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tQ) e.symm ?_
    simp only [Iso.symm_inv, e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]
  exact (SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact 1).of_isPullback
    (IsPullback.of_hasPullback s (pullback.snd c tK)) hQ ‹_›

theorem ofPoint_I_congr {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (ha : a ≫ f = g) (ha' : a' ≫ f = g) (h : a = a') :
    (RelEffCartierDiv.ofPoint f a ha).I = (RelEffCartierDiv.ofPoint f a' ha').I := by
  subst h; rfl

def invUnique {X : Scheme.{u}} {L M M' : X.Modules} (e : L ⊗ M ≅ 𝟙_ X.Modules) (e' : L ⊗ M' ≅ 𝟙_ X.Modules) : M ≅ M' :=
  (λ_ M).symm ≪≫ whiskerRightIso (β_ M' L ≪≫ e').symm M ≪≫ α_ M' L M ≪≫ whiskerLeftIso M' e ≪≫ ρ_ M'

theorem nonempty_pullback_module_iso {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} {J : X'.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (e : (Scheme.Modules.pullback f).obj I.invModule ≅ J.invModule) :
    Nonempty ((Scheme.Modules.pullback f).obj I.module ≅ J.module) := by

  obtain ⟨eI⟩ := (Scheme.Modules.IsInvertible.dual (Scheme.IdealSheafData.IsInvertible.isInvertible_module hI)).2
  obtain ⟨eJ⟩ := (Scheme.Modules.IsInvertible.dual (Scheme.IdealSheafData.IsInvertible.isInvertible_module hJ)).2
  have e1 : J.invModule ⊗ (Scheme.Modules.pullback f).obj I.module ≅ 𝟙_ _ :=
    whiskerRightIso e.symm _ ≪≫ (β_ _ _) ≪≫ (Scheme.Modules.pullbackTensorObjIso f _ _).symm ≪≫
      (Scheme.Modules.pullback f).mapIso eI ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f
  have e2 : J.invModule ⊗ J.module ≅ 𝟙_ _ := β_ _ _ ≪≫ eJ
  exact ⟨invUnique e1 e2⟩

theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp only [pow_zero]; try exact Scheme.IdealSheafData.comap_top f
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

theorem smoothRelDimOne_descend {X S S' : Scheme.{u}} (g : X ⟶ S) (f : S' ⟶ S)
    (hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f)
    [SmoothOfRelativeDimension 1 (pullback.fst f g)] : SmoothOfRelativeDimension 1 g :=
  (SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact 1).of_isPullback
    (IsPullback.of_hasPullback f g) hQ ‹_›

theorem geometricallyIntegral_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [GeometricallyIntegral f] : GeometricallyIntegral g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral e.inv f).mpr ‹_›

theorem locallyOfFiniteType_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [LocallyOfFiniteType f] : LocallyOfFiniteType g := by
  rw [← he]; infer_instance

theorem isSeparated_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [IsSeparated f] : IsSeparated g := by
  rw [← he]; infer_instance

end K6aKit

namespace K6Kit

section ClassGroup

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

variable (c ε) in

def topGrp : SubPicGroupCondition c ε where
  toSubPicCondition := SubPicCondition.top c ε
  tensor_mem := fun _ _ _ _ _ => trivial
  inv_mem := fun _ _ _ _ _ => trivial

variable (c ε) in

abbrev Cl {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : Type (u + 1) :=
  (relSubPicPresheaf c ε (topGrp c ε).toSubPicCondition).obj (op (Over.mk t))

scoped instance instCommGroupCl {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (Cl c ε t) :=
  (topGrp c ε).commGroupObj (op (Over.mk t))

def cl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) : Cl c ε t :=
  ⟨Quotient.mk _ M, trivial⟩

theorem cl_eq_iff {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t) :
    cl M = cl N ↔ Nonempty (M.L ≅ N.L) := by
  constructor
  · intro h
    exact Quotient.exact (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Quotient.sound h)

theorem cl_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {M N : RigidifiedLineBundle c ε t}
    (h : Nonempty (M.L ≅ N.L)) : cl M = cl N :=
  (cl_eq_iff M N).2 h

theorem cl_tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t) :
    cl (M.tensor N) = cl M * cl N := rfl

theorem cl_unit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    cl (RigidifiedLineBundle.unit (c := c) (ε := ε) t) = 1 := rfl

theorem cl_eq_one_of_mul_self {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : Cl c ε t)
    (h : x * x = x) : x = 1 :=
  mul_left_cancel (a := x) (h.trans (mul_one x).symm)

variable {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}

theorem homEquiv_coe (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (g : Over.mk t ⟶ Over.mk D.toBase) :
    (h.representableBy.homEquiv g).1 = Quotient.mk _ (h.poincare.pullbackAlong ⟨g.left, Over.w g⟩) := rfl

theorem mul_classify (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M₁ M₂ : RigidifiedLineBundle c ε t) (h₁ : P.P t M₁) (h₂ : P.P t M₂) :
    h.relativeGroupLaw.mul t (h.classify t M₁ h₁) (h.classify t M₂ h₂)
      = h.classify t (M₁.tensor M₂) (P.tensor_mem t M₁ M₂ h₁ h₂) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk t))
  set a : Over.mk t ⟶ Over.mk D.toBase := schemeHomOverToOverHom (h.classify t M₁ h₁) with ha
  set b : Over.mk t ⟶ Over.mk D.toBase := schemeHomOverToOverHom (h.classify t M₂ h₂) with hb
  have hmul : h.relativeGroupLaw.mul t (h.classify t M₁ h₁) (h.classify t M₂ h₂) = overHomToSchemeHomOver (a * b) := rfl
  rw [hmul]
  apply h.classify_unique
  have key := congrArg Subtype.val (h.homEquiv_mul (Over.mk t) a b)
  rw [homEquiv_coe] at key
  have ka : (h.representableBy.homEquiv a).1 = Quotient.mk _ M₁ := by
    rw [homEquiv_coe]; exact Quotient.sound (h.classify_spec t M₁ h₁)
  have kb : (h.representableBy.homEquiv b).1 = Quotient.mk _ M₂ := by
    rw [homEquiv_coe]; exact Quotient.sound (h.classify_spec t M₂ h₂)
  have kab : (h.representableBy.homEquiv a * h.representableBy.homEquiv b).1
      = Quotient.mk _ (M₁.tensor M₂) := by
    show Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
      (h.representableBy.homEquiv a).1 (h.representableBy.homEquiv b).1 = _
    rw [ka, kb]
    rfl
  rw [kab] at key
  exact Quotient.exact key

def pcl (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t D.toBase) : Cl c ε t :=
  cl (h.poincare.pullbackAlong x)

theorem pcl_mul (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t D.toBase) :
    pcl h (h.relativeGroupLaw.mul t x y) = pcl h x * pcl h y := by
  have hx : x = h.classify t (h.poincare.pullbackAlong x) (P.pullback_mem _ _ x _ h.poincare_mem) :=
    h.classify_unique t _ _ x ⟨Iso.refl _⟩
  have hy : y = h.classify t (h.poincare.pullbackAlong y) (P.pullback_mem _ _ y _ h.poincare_mem) :=
    h.classify_unique t _ _ y ⟨Iso.refl _⟩
  unfold pcl
  rw [← cl_tensor]
  apply cl_congr
  have e1 := mul_classify h t (h.poincare.pullbackAlong x) (h.poincare.pullbackAlong y)
    (P.pullback_mem _ _ x _ h.poincare_mem) (P.pullback_mem _ _ y _ h.poincare_mem)
  rw [← hx, ← hy] at e1
  rw [e1]
  exact h.classify_spec t _ _

theorem pcl_injective (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {x y : SchemeHomOver t D.toBase} (hxy : pcl h x = pcl h y) : x = y :=
  h.ext_of_iso t x y ((cl_eq_iff _ _).1 hxy)

def pclHom (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := h.relativeGroupLaw.pointGroup t
    SchemeHomOver t D.toBase →* Cl c ε t :=
  letI := h.relativeGroupLaw.pointGroup t
  MonoidHom.mk' (pcl h) (pcl_mul h t)

end ClassGroup

section Rig

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {K : Type u} [Field K]
  {t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)}

variable (ε t) in

def rig (L : (pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) : RigidifiedLineBundle c ε t where
  L := L
  isInvertible := hL
  rigidified := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _ (hL.pullback _)

theorem cl_rig_congr {L M : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (e : Nonempty (L ≅ M)) : cl (rig ε t L hL) = cl (rig ε t M hM) :=
  cl_congr e

theorem cl_rig_tensor {L M : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) :
    cl (rig ε t (L ⊗ M) (hL.tensor hM)) = cl (rig ε t L hL) * cl (rig ε t M hM) :=
  cl_congr ⟨Iso.refl _⟩

theorem cl_rig_unit : cl (rig ε t (𝟙_ _) (Scheme.Modules.isInvertible_unit _)) = 1 :=
  cl_congr ⟨Iso.refl _⟩

theorem cl_rig_L (M : RigidifiedLineBundle c ε t) : cl (rig ε t M.L M.isInvertible) = cl M :=
  cl_congr ⟨Iso.refl _⟩

theorem cl_rig_tensor' {L M : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (hLM : Scheme.Modules.IsInvertible (L ⊗ M)) :
    cl (rig ε t (L ⊗ M) hLM) = cl (rig ε t L hL) * cl (rig ε t M hM) :=
  cl_congr ⟨Iso.refl _⟩

theorem cl_rig_unit' (h : Scheme.Modules.IsInvertible (𝟙_ (pullback c t).Modules)) : cl (rig ε t (𝟙_ _) h) = 1 :=
  cl_congr ⟨Iso.refl _⟩

theorem cl_rig_irrel {L : (pullback c t).Modules} (h h' : Scheme.Modules.IsInvertible L) : cl (rig ε t L h) = cl (rig ε t L h') := rfl

theorem isInvertible_of_iso {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M) (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  exact ⟨U, hxU, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ eU⟩⟩

variable (ε t) in

def clI (I : (pullback c t).IdealSheafData) (hI : I.IsInvertible) : Cl c ε t :=
  cl (rig ε t I.invModule hI.isInvertible_invModule)

variable (ε t) in

def clM (I : (pullback c t).IdealSheafData) (hI : I.IsInvertible) : Cl c ε t :=
  cl (rig ε t I.module hI.isInvertible_module)

theorem clI_congr {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    clI ε t I hI = clI ε t J hJ := by subst h; rfl

theorem clM_congr {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    clM ε t I hI = clM ε t J hJ := by subst h; rfl

theorem clM_mul_clI {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) : clM ε t I hI * clI ε t I hI = 1 := by
  unfold clM clI
  rw [← cl_rig_tensor, ← cl_rig_unit (ε := ε) (t := t)]
  exact cl_congr hI.isInvertible_module.dual.2

theorem clI_eq_inv {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) : clI ε t I hI = (clM ε t I hI)⁻¹ :=
  eq_inv_of_mul_eq_one_right (clM_mul_clI hI)

theorem clM_eq_inv {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) : clM ε t I hI = (clI ε t I hI)⁻¹ := by
  rw [clI_eq_inv, inv_inv]

theorem clI_mul {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (hIJ : (I * J).IsInvertible) :
    clI ε t (I * J) hIJ = clI ε t I hI * clI ε t J hJ := by
  unfold clI
  rw [← cl_rig_tensor]
  exact cl_congr (hI.nonempty_mul_invModule_iso_tensor hJ)

theorem clM_mul {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (hIJ : (I * J).IsInvertible) :
    clM ε t (I * J) hIJ = clM ε t I hI * clM ε t J hJ := by
  unfold clM
  rw [← cl_rig_tensor]
  exact cl_congr (hI.nonempty_mul_module_iso_tensor hJ)

theorem clI_one {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) :
    clI ε t 1 (by simpa using hI.pow 0) = 1 := by
  apply cl_eq_one_of_mul_self
  have h1 : (1 : (pullback c t).IdealSheafData).IsInvertible := by simpa using hI.pow 0
  rw [← clI_mul h1 h1 (by simpa using h1)]
  exact clI_congr _ _ (mul_one 1)

theorem clM_one {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) :
    clM ε t 1 (by simpa using hI.pow 0) = 1 := by
  apply cl_eq_one_of_mul_self
  have h1 : (1 : (pullback c t).IdealSheafData).IsInvertible := by simpa using hI.pow 0
  rw [← clM_mul h1 h1 (by simpa using h1)]
  exact clM_congr _ _ (mul_one 1)

theorem clI_pow {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    clI ε t (I ^ n) (hI.pow n) = clI ε t I hI ^ n := by
  induction n with
  | zero => rw [pow_zero (clI ε t I hI)]; exact (clI_congr _ _ (pow_zero I)).trans (clI_one hI)
  | succ n ih =>
    rw [pow_succ (clI ε t I hI) n, ← ih]
    have hJ : (I ^ n * I).IsInvertible := by rw [← pow_succ]; exact hI.pow (n + 1)
    exact (clI_congr _ hJ (pow_succ I n)).trans (clI_mul (hI.pow n) hI hJ)

theorem clM_pow {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    clM ε t (I ^ n) (hI.pow n) = clM ε t I hI ^ n := by
  induction n with
  | zero => rw [pow_zero (clM ε t I hI)]; exact (clM_congr _ _ (pow_zero I)).trans (clM_one hI)
  | succ n ih =>
    rw [pow_succ (clM ε t I hI) n, ← ih]
    have hJ : (I ^ n * I).IsInvertible := by rw [← pow_succ]; exact hI.pow (n + 1)
    exact (clM_congr _ hJ (pow_succ I n)).trans (clM_mul (hI.pow n) hI hJ)

end Rig

end K6Kit
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero.K6Kit"

namespace K5Kit

open K6aKit

set_option maxHeartbeats 3200000 in

theorem genTransport
    (p : ℕ) [Fact p.Prime] [IsProper (DRModel.toBase p)] (O : Type) [CommRing O] [IsDomain O] (hpO : ((p : ℕ) : O) ≠ 0)
    (Y : Scheme.{0}) (toBase : Y ⟶ Spec (CommRingCat.of O))
    (toDR : Y ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (toDR_over : toDR ≫ pullback.snd _ _ = toBase) [IsProper toBase]
    (toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))))
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) toBase) (pos neg : Fin m → ℕ)
    (hLgen : Nonempty ((Scheme.Modules.pullback (pullback.fst toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))) ≫ toDR)).obj M ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)))
    (K : Type) [Field K] (τ : O →+* K) (τF : FractionRing O →+* K) (hτ : τF.comp (algebraMap O (FractionRing O)) = τ)
    (tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ))
    (htK : Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) = tK)
    [SmoothOfRelativeDimension 1 (pullback.snd (DRModel.toBase p) tK)]
    [SmoothOfRelativeDimension 1 (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (FractionRing O)))))]
    (hx : ∀ j, ((Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) ≫ DRModel.toBase p = tK) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd (DRModel.toBase p)
        (⟨Spec.map (CommRingCat.ofHom τ), htK⟩ : SchemeHomOver tK (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))).obj M ≅
      (List.finRange m).foldr (fun j N =>
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _)
              (hx j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _)
              (hx j)).I ^ (neg j)).module ⊗ N)
        (𝟙_ (pullback (DRModel.toBase p) tK).Modules)) := by
  subst toDR_over
  obtain ⟨hL⟩ := hLgen

  let F := FractionRing O
  let c := DRModel.toBase p
  let tO : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let c' := toDR ≫ pullback.snd c tO
  let tZF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ F))
  let tb : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom τ)
  let tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O F))
  let sF : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom τF)
  have htb : tb ≫ tO = tK := htK
  have htF : tF ≫ tO = tZF := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; all_goals (congr 2; exact RingHom.ext_int _ _)
  have hsF : sF ≫ tF = tb := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]

  have hpF : algebraMap O F (p : O) ≠ 0 := fun h =>
    hpO ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective O F) _ h)
  have hτp : τ (p : O) ≠ 0 := by
    rw [← hτ, RingHom.comp_apply]
    exact (map_ne_zero τF).2 hpF
  let U : (Spec (CommRingCat.of O)).Opens := PrimeSpectrum.basicOpen ((p : ℕ) : O)
  have hmemU : ∀ {K' : Type} [Field K'] (f : O →+* K'), f (p : O) ≠ 0 →
      Set.range (Spec.map (CommRingCat.ofHom f)).base ⊆ (U : Set _) := by
    intro K' _ f hf
    rintro _ ⟨x, rfl⟩
    have hx0 : x.asIdeal = ⊥ := (Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top
    show ((p : ℕ) : O) ∉ ((Spec.map (CommRingCat.ofHom f)).base x).asIdeal
    rw [Spec.map_base]
    show ((p : ℕ) : O) ∉ Ideal.comap f x.asIdeal
    rw [hx0, Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  have mkIso : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of O)) (ht : Set.range t.base ⊆ (U : Set _))
      (t' : T ⟶ Spec (CommRingCat.of ℤ)) (htt : t ≫ tO = t'),
      ∃ eY : pullback c' t ≅ pullback c t',
        eY.hom ≫ pullback.snd c t' = pullback.snd c' t ∧
        eY.hom ≫ pullback.fst c t' = pullback.fst c' t ≫ toDR ≫ pullback.fst c tO := by
    intro T t ht t' htt
    subst htt
    let h := pullback.fst (pullback.snd c tO) t
    have hh : Set.range h.base ⊆ ((pullback.snd c tO ⁻¹ᵁ U : (pullback c tO).Opens) : Set _) := by
      rintro _ ⟨x, rfl⟩
      show (h ≫ pullback.snd c tO).base x ∈ (U : Set _)
      rw [pullback.condition]
      exact ht ⟨_, rfl⟩
    haveI : IsIso (pullback.snd toDR h) := K6aKit.isIso_pullback_snd_of_isIso_morphismRestrict toDR _ h hh
    let e2 : pullback c' t ≅ pullback toDR h := (pullbackRightPullbackFstIso (pullback.snd c tO) t toDR).symm
    let e4 : pullback toDR h ≅ pullback (pullback.snd c tO) t := asIso (pullback.snd toDR h)
    let e5 : pullback (pullback.snd c tO) t ≅ pullback c (t ≫ tO) := pullbackLeftPullbackSndIso c tO t
    refine ⟨e2 ≪≫ e4 ≪≫ e5, ?_, ?_⟩
    · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, asIso_hom,
        Iso.symm_hom, pullbackRightPullbackFstIso_inv_snd_snd]
    · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, asIso_hom,
        ← pullback.condition_assoc, Iso.symm_hom, pullbackRightPullbackFstIso_inv_fst_assoc]
  obtain ⟨eY, heY1, heY2⟩ := mkIso tb (hmemU τ hτp) tK htb
  obtain ⟨eYF, heYF1, heYF2⟩ := mkIso tF (hmemU (algebraMap O F) hpF) tZF htF
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c' tb) :=
    K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tK) eY.symm heY1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c' tF) :=
    K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tZF) eYF.symm heYF1

  have hIF : ∀ j, (sectionIdeal c' (σ j) tF).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' tF) _ (pullback.lift_snd _ _ _)
  have hIb : ∀ j, (sectionIdeal c' (σ j) tb).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' tb) _ (pullback.lift_snd _ _ _)
  have hIX : ∀ j, (RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I.IsInvertible :=
    fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tK) _ (graphOver_snd _ _ _)

  let ψb : SchemeHomOver tK tO := ⟨tb, htb⟩
  let bO := baseChangeSnd c ψb
  have heYbO : eY.hom ≫ bO = pullback.fst c' tb ≫ toDR := by
    apply pullback.hom_ext
    · rw [Category.assoc, BaseChange.baseChangeSnd_fst', heY2, Category.assoc]
    · rw [Category.assoc, BaseChange.baseChangeSnd_snd', reassoc_of% heY1, Category.assoc, pullback.condition]
  let ψF : SchemeHomOver tb tF := ⟨sF, hsF⟩
  let bF := baseChangeSnd c' ψF
  have PB : (Scheme.Modules.pullback eY.hom).obj ((Scheme.Modules.pullback bO).obj M) ≅
      (Scheme.Modules.pullback bF).obj ((List.finRange m).foldr
          (fun j N => (sectionTwist c' (σ j) tF (pos j) ⊗ ((sectionIdeal c' (σ j) tF) ^ (neg j)).module) ⊗ N) (𝟙_ _)) :=
    (Scheme.Modules.pullbackComp eY.hom bO).app M ≪≫
      (Scheme.Modules.pullbackCongr heYbO).app M ≪≫
      (Scheme.Modules.pullbackCongr (show pullback.fst c' tb ≫ toDR = bF ≫ (pullback.fst c' tF ≫ toDR) by
        rw [← Category.assoc, BaseChange.baseChangeSnd_fst'])).app M ≪≫
      ((Scheme.Modules.pullbackComp bF (pullback.fst c' tF ≫ toDR)).app M).symm ≪≫
      (Scheme.Modules.pullback bF).mapIso hL

  have hcomap : ∀ j (n : ℕ), ((sectionIdeal c' (σ j) tF) ^ n).comap bF = (sectionIdeal c' (σ j) tb) ^ n := by
    intro j n
    rw [K6aKit.comap_pow]
    congr 1
    have h1 := congrArg RelEffCartierDiv.I
      (RelEffCartierDiv.pullbackAlong_ofPoint c' (tF ≫ (σ j).1)
        (by rw [Category.assoc, (σ j).2, Category.comp_id]) sF hsF)
    have h2 : (RelEffCartierDiv.ofPoint c' (sF ≫ tF ≫ (σ j).1) (by rw [Category.assoc, Category.assoc, (σ j).2, Category.comp_id, hsF])).I =
        (RelEffCartierDiv.ofPoint c' (tb ≫ (σ j).1) (by rw [Category.assoc, (σ j).2, Category.comp_id])).I :=
      K6aKit.ofPoint_I_congr _ _ (by rw [← Category.assoc, hsF])
    exact h1.trans h2
  have jA : ∀ j (n : ℕ), Nonempty ((Scheme.Modules.pullback bF).obj (((sectionIdeal c' (σ j) tF) ^ n).invModule) ≅
      ((sectionIdeal c' (σ j) tb) ^ n).invModule) := by
    intro j n
    have hI' : ((((sectionIdeal c' (σ j) tF) ^ n).comap bF)).IsInvertible := by rw [hcomap]; exact (hIb j).pow n
    obtain ⟨e⟩ := ((hIF j).pow n).nonempty_pullback_invModule_iso bF hI'
    exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hcomap j n))⟩
  have jB : ∀ j (n : ℕ), Nonempty ((Scheme.Modules.pullback bF).obj (((sectionIdeal c' (σ j) tF) ^ n).module) ≅
      ((sectionIdeal c' (σ j) tb) ^ n).module) := fun j n =>
    K6aKit.nonempty_pullback_module_iso bF ((hIF j).pow n) ((hIb j).pow n) (jA j n).some
  have PC : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback bF).obj (l.foldr
        (fun j N => (sectionTwist c' (σ j) tF (pos j) ⊗ ((sectionIdeal c' (σ j) tF) ^ (neg j)).module) ⊗ N) (𝟙_ _)) ≅
      l.foldr (fun j N => (sectionTwist c' (σ j) tb (pos j) ⊗ ((sectionIdeal c' (σ j) tb) ^ (neg j)).module) ⊗ N) (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact ⟨Scheme.Modules.pullbackTensorUnitObjIso bF⟩
    | cons j l ih =>
      exact ⟨Scheme.Modules.pullbackTensorObjIso bF _ _ ≪≫
        ((Scheme.Modules.pullbackTensorObjIso bF _ _ ≪≫ ((jA j (pos j)).some ⊗ᵢ (jB j (neg j)).some)) ⊗ᵢ ih.some)⟩

  have hσb : ∀ j, (tb ≫ (σ j).1) ≫ c' = tb := fun j => by rw [Category.assoc, (σ j).2, Category.comp_id]
  have hgraph : ∀ j, graphOver c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j) ≫ eY.inv =
      graphOver c' (tb ≫ (σ j).1) (hσb j) := by
    intro j
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc (graphOver c' _ _) eY.hom (pullback.fst c tK), heY2, graphOver_fst_assoc]
    · rw [graphOver_snd, Category.assoc (graphOver c' _ _) eY.hom (pullback.snd c tK), heY1, graphOver_snd]
  have jX : ∀ j (n : ℕ),
      Nonempty ((Scheme.Modules.pullback eY.inv).obj (((sectionIdeal c' (σ j) tb) ^ n).invModule) ≅
        ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback eY.inv).obj (((sectionIdeal c' (σ j) tb) ^ n).module) ≅
        ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ n).module) :=
    fun j n => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso eY.inv _ _ (hgraph j) (hIb j) (hIX j) n
  have PD : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback eY.inv).obj (l.foldr
        (fun j N => (sectionTwist c' (σ j) tb (pos j) ⊗ ((sectionIdeal c' (σ j) tb) ^ (neg j)).module) ⊗ N) (𝟙_ _)) ≅
      l.foldr (fun j N =>
          ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ (neg j)).module ⊗ N)
        (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact ⟨Scheme.Modules.pullbackTensorUnitObjIso eY.inv⟩
    | cons j l ih =>
      exact ⟨Scheme.Modules.pullbackTensorObjIso eY.inv _ _ ≪≫
        ((Scheme.Modules.pullbackTensorObjIso eY.inv _ _ ≪≫ ((jX j (pos j)).1.some ⊗ᵢ (jX j (neg j)).2.some)) ⊗ᵢ ih.some) ≪≫
        α_ _ _ _⟩
  have undo : (Scheme.Modules.pullback bO).obj M ≅
      (Scheme.Modules.pullback eY.inv).obj ((Scheme.Modules.pullback eY.hom).obj ((Scheme.Modules.pullback bO).obj M)) :=
    ((Scheme.Modules.pullbackId _).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr eY.inv_hom_id.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp eY.inv eY.hom).app _).symm
  exact ⟨undo ≪≫ (Scheme.Modules.pullback eY.inv).mapIso (PB ≪≫ (PC _).some) ≪≫ (PD _).some⟩

end K5Kit
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero.K6Kit"

end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero.K6Kit"

set_option maxHeartbeats 6400000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges)
    (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (hMinv : Scheme.Modules.IsInvertible M)
    (eMgen : Nonempty ((Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))) ≫ 𝔛reg.toDR)).obj M ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)))
    (hsp : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O)),
      IsLocalRing.closedPoint O ∈ Set.range s.base →
      IsAlgEquivZero (fibreAt (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) s)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (DRModel.toBase p)
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) s)).obj M)) :
    ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong z).L ≅ M) := by
  classical
  haveI := 𝔛.isProper
  haveI := 𝔛.eη_iso
  let c := DRModel.toBase p
  let tO : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let ε := 𝔛.εinf

  have hrig : Nonempty ((Scheme.Modules.pullback (rigSection c tO ε)).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of O)).ringCatSheaf) :=
    Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing (hMinv.pullback _)
  let Mr : RigidifiedLineBundle c ε tO := ⟨M, hMinv, hrig⟩

  have hpO : ((p : ℕ) : O) ≠ 0 := fun h =>
    IsDiscreteValuationRing.not_a_field O (by rw [hϖ]; exact Ideal.span_singleton_eq_bot.2 h)

  have hcharO : CharZero O := by
    obtain ⟨ℓ, hℓ⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O ℓ with hℓp | rfl
    · exfalso
      by_cases hlp : ℓ = p
      · subst hlp; exact hpO (CharP.cast_eq_zero O ℓ)
      · have hcop : IsCoprime ((ℓ : ℤ) : O) ((p : ℤ) : O) :=
          (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hℓp Fact.out).2 hlp)).map (Int.castRingHom O)
        rw [Int.cast_natCast, Int.cast_natCast, CharP.cast_eq_zero O ℓ, isCoprime_zero_left] at hcop
        have hmem : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by rw [hϖ]; exact Ideal.mem_span_singleton_self _
        exact (IsLocalRing.mem_maximalIdeal _).1 hmem hcop
    · exact CharP.charP_to_charZero O

  have hF : FibrewiseAlgEquivZero Mr := by
    intro k _ _ s
    obtain ⟨φ, rfl⟩ : ∃ φ : O →+* k, s = Spec.map (CommRingCat.ofHom φ) := ⟨(Spec.preimage s).hom, by simp⟩
    by_cases hker : Function.Injective φ
    ·
      let F := FractionRing O
      let τF : F →+* k := IsFractionRing.lift hker
      have hτ : τF.comp (algebraMap O F) = φ := RingHom.ext fun x => IsFractionRing.lift_algebraMap hker x
      let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom φ)
      let tk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ) := s ≫ tO

      haveI : CharZero k := charZero_of_injective_ringHom hker
      let ιQ : AlgebraicClosure ℚ →+* k := (IsAlgClosed.lift (R := ℚ) (M := k) (S := AlgebraicClosure ℚ)).toRingHom
      let tQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℤ) :=
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))
      let sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)) := Spec.map (CommRingCat.ofHom ιQ)
      have hsk : sk ≫ tQ = tk := by
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2; exact RingHom.ext_int _ _

      haveI hsmQ : SmoothOfRelativeDimension 1 (pullback.snd c tQ) :=
        K6aKit.smoothOfRelativeDimension_one_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη)
          (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])
      haveI : GeometricallyIntegral 𝔛.Mη.toBase := geometricallyIntegral_of_isAlgClosed _
      haveI hgiQ : GeometricallyIntegral (pullback.snd c tQ) :=
        K6aKit.geometricallyIntegral_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη)
          (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])
      let ek : pullback (pullback.snd c tQ) sk ≅ pullback c tk := pullbackLeftPullbackSndIso c tQ sk ≪≫ pullback.congrHom rfl hsk
      have hek : ek.hom ≫ pullback.snd c tk = pullback.snd (pullback.snd c tQ) sk := by
        simp only [ek, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
          pullbackLeftPullbackSndIso_hom_snd]
      haveI hsmk : SmoothOfRelativeDimension 1 (pullback.snd c tk) :=
        K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd (pullback.snd c tQ) sk) ek (by rw [Iso.inv_comp_eq, hek])
      haveI hgik : GeometricallyIntegral (pullback.snd c tk) :=
        K6aKit.geometricallyIntegral_of_iso (f := pullback.snd (pullback.snd c tQ) sk) ek (by rw [Iso.inv_comp_eq, hek])

      let tZF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ F))
      let sF : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom τF)
      have hsF : sF ≫ tZF = tk := by
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2; exact RingHom.ext_int _ _
      let eF : pullback sF (pullback.snd c tZF) ≅ pullback c tk :=
        pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso c tZF sF ≪≫ pullback.congrHom rfl hsF
      haveI : SmoothOfRelativeDimension 1 (pullback.fst sF (pullback.snd c tZF)) := by
        refine K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tk) eF.symm ?_
        simp only [Iso.symm_inv, eF, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
          Category.comp_id, pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]
      haveI hsmF : SmoothOfRelativeDimension 1 (pullback.snd c tZF) :=
        K6aKit.smoothRelDimOne_descend _ sF ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

      have hx : ∀ j, ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _) ≫ DRModel.toBase p = tk := fun j => by
        rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛reg.toDR_over, reassoc_of% (σ j).2]
      obtain ⟨eT⟩ := K5Kit.genTransport p O hpO 𝔛reg.Y 𝔛reg.toBase 𝔛reg.toDR 𝔛reg.toDR_over 𝔛reg.toDR_iso_generic M m σ pos neg
        eMgen k φ τF hτ tk rfl hx

      let XOs := pullback (pullback.snd c tO) s
      let a : XOs ⟶ Spec (CommRingCat.of k) := pullback.snd (pullback.snd c tO) s
      show IsAlgEquivZero a ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tO) s)).obj M)
      let κs : XOs ≅ pullback c tk := pullbackLeftPullbackSndIso c tO s
      have hκs1 : κs.hom ≫ pullback.snd c tk = a := pullbackLeftPullbackSndIso_hom_snd _ _ _
      have hκs2 : κs.hom ≫ pullback.fst c tk = pullback.fst (pullback.snd c tO) s ≫ pullback.fst c tO :=
        pullbackLeftPullbackSndIso_hom_fst _ _ _
      haveI : SmoothOfRelativeDimension 1 a :=
        K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tk) κs.symm hκs1
      haveI : GeometricallyIntegral a := K6aKit.geometricallyIntegral_of_iso (f := pullback.snd c tk) κs.symm hκs1
      haveI instSep : IsSeparated a := inferInstance
      haveI instLft : LocallyOfFiniteType a := inferInstance
      haveI : IsIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k)))) := inferInstance

      let bk := baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver tk tO)
      have hκbk : κs.hom ≫ bk = pullback.fst (pullback.snd c tO) s := by
        apply pullback.hom_ext
        · rw [Category.assoc, BaseChange.baseChangeSnd_fst', hκs2]
        · rw [Category.assoc, BaseChange.baseChangeSnd_snd', reassoc_of% hκs1, pullback.condition]
      let Ls := (Scheme.Modules.pullback (pullback.fst (pullback.snd c tO) s)).obj M
      let θ : pullback a (𝟙 _) ⟶ pullback c tk := pullback.fst a (𝟙 _) ≫ κs.hom
      haveI : IsIso θ := IsIso.comp_isIso
      have e2 : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj Ls ≅ (Scheme.Modules.pullback θ).obj
          ((List.finRange m).foldr (fun j N =>
            ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _)
              (hx j)).I ^ (pos j)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _)
              (hx j)).I ^ (neg j)).module ⊗ N) (𝟙_ _)) :=
        (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).mapIso
            ((Scheme.Modules.pullbackCongr hκbk.symm).app M ≪≫ ((Scheme.Modules.pullbackComp κs.hom bk).app M).symm ≪≫
              (Scheme.Modules.pullback κs.hom).mapIso eT) ≪≫
          (Scheme.Modules.pullbackComp (pullback.fst a (𝟙 _)) κs.hom).app _

      have hPt : ∀ j, (s ≫ (σ j).1 ≫ 𝔛reg.toDR) ≫ pullback.snd c tO = 𝟙 _ ≫ s := fun j => by
        rw [Category.assoc, Category.assoc, 𝔛reg.toDR_over, (σ j).2, Category.comp_id, Category.id_comp]
      let Pt : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a := fun j =>
        ⟨pullback.lift (s ≫ (σ j).1 ≫ 𝔛reg.toDR) (𝟙 _) (hPt j), pullback.lift_snd _ _ _⟩
      have hεt : (s ≫ rigSection c tO ε) ≫ pullback.snd c tO = 𝟙 _ ≫ s := by
        rw [Category.assoc, BaseChange.rigSection_snd', Category.comp_id, Category.id_comp]
      let εt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a := ⟨pullback.lift (s ≫ rigSection c tO ε) (𝟙 _) hεt, pullback.lift_snd _ _ _⟩

      have hgraph : ∀ j, graphOver a (Pt j).1 (Pt j).2 ≫ θ =
          graphOver c ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j) := by
        intro j
        apply pullback.hom_ext
        · rw [graphOver_fst, Category.assoc, Category.assoc (pullback.fst a _), hκs2, graphOver_fst_assoc]
          show pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
          rw [pullback.lift_fst_assoc]
          simp only [Category.assoc]
          rfl
        · rw [graphOver_snd, Category.assoc, Category.assoc (pullback.fst a _), hκs1, pullback.condition, graphOver_snd_assoc]
      have hε2 : (tk ≫ ε.1) ≫ c = tk := by rw [Category.assoc, ε.2, Category.comp_id]
      have hgraphε : graphOver a εt.1 εt.2 ≫ θ = graphOver c (tk ≫ ε.1) hε2 := by
        apply pullback.hom_ext
        · rw [graphOver_fst, Category.assoc, Category.assoc (pullback.fst a _), hκs2, graphOver_fst_assoc]
          show pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
          rw [pullback.lift_fst_assoc, Category.assoc, BaseChange.rigSection_fst']
          rfl
        · rw [graphOver_snd, Category.assoc, Category.assoc (pullback.fst a _), hκs1, pullback.condition, graphOver_snd_assoc]

      have hIk : ∀ j, (RelEffCartierDiv.ofPoint c ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I.IsInvertible :=
        fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tk) _ (graphOver_snd _ _ _)
      have hIP : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a, (RelEffCartierDiv.ofPoint a P.1 P.2).I.IsInvertible :=
        fun P => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd a (𝟙 _)) _ (graphOver_snd _ _ _)
      have jP : ∀ j (n : ℕ),
          Nonempty ((Scheme.Modules.pullback θ).obj
            (((RelEffCartierDiv.ofPoint c ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ n).invModule) ≅
            ((RelEffCartierDiv.ofPoint a (Pt j).1 (Pt j).2).I ^ n).invModule) ∧
          Nonempty ((Scheme.Modules.pullback θ).obj
            (((RelEffCartierDiv.ofPoint c ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ n).module) ≅
            ((RelEffCartierDiv.ofPoint a (Pt j).1 (Pt j).2).I ^ n).module) :=
        fun j n => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso θ _ _ (hgraph j) (hIk j) (hIP (Pt j)) n
      let I : Fin m → (pullback a (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun j => (RelEffCartierDiv.ofPoint a (Pt j).1 (Pt j).2).I
      let Iε : (pullback a (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := (RelEffCartierDiv.ofPoint a εt.1 εt.2).I
      let FoldP : List (Fin m) → (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules := fun l =>
        l.foldr (fun j N => ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module ⊗ N) (𝟙_ _)
      have PDk : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback θ).obj (l.foldr (fun j N =>
            ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _)
              (hx j)).I ^ (pos j)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((s ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) _)
              (hx j)).I ^ (neg j)).module ⊗ N) (𝟙_ _)) ≅ FoldP l) := by
        intro l
        induction l with
        | nil => exact ⟨Scheme.Modules.pullbackTensorUnitObjIso θ⟩
        | cons j l ih =>
          exact ⟨Scheme.Modules.pullbackTensorObjIso θ _ _ ≪≫
            ((jP j (pos j)).1.some ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso θ _ _ ≪≫ ((jP j (neg j)).2.some ⊗ᵢ ih.some)))⟩
      have eP : Nonempty ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj Ls ≅ FoldP (List.finRange m)) := ⟨e2 ≪≫ (PDk _).some⟩

      have hI : ∀ j, (I j).IsInvertible := fun j => hIP (Pt j)
      have hIε : Iε.IsInvertible := hIP εt
      let Og : Fin m → K6Kit.Cl a εt (𝟙 (Spec (CommRingCat.of k))) := fun j => K6Kit.clI εt (𝟙 (Spec (CommRingCat.of k))) (I j) (hI j)
      let E : K6Kit.Cl a εt (𝟙 (Spec (CommRingCat.of k))) := K6Kit.clM εt (𝟙 (Spec (CommRingCat.of k))) Iε hIε
      have hFinv : ∀ l : List (Fin m), Scheme.Modules.IsInvertible (FoldP l) := by
        intro l
        induction l with
        | nil => exact Scheme.Modules.isInvertible_unit _
        | cons j l ih => exact ((hI j).pow (pos j)).isInvertible_invModule.tensor (((hI j).pow (neg j)).isInvertible_module.tensor ih)
      have hFcl : ∀ l : List (Fin m), K6Kit.cl (K6Kit.rig εt (𝟙 (Spec (CommRingCat.of k))) (FoldP l) (hFinv l)) =
          (l.map fun j => Og j ^ (pos j) * (Og j)⁻¹ ^ (neg j)).prod := by
        intro l
        induction l with
        | nil => exact K6Kit.cl_rig_unit' _
        | cons j l ih =>
          rw [List.map_cons, List.prod_cons, ← ih, mul_assoc, ← K6Kit.clI_pow (hI j), ← K6Kit.clM_eq_inv (hI j), ← K6Kit.clM_pow (hI j)]
          exact (K6Kit.cl_rig_tensor' (ε := εt) ((hI j).pow (pos j)).isInvertible_invModule
              (((hI j).pow (neg j)).isInvertible_module.tensor (hFinv l)) _).trans
            (congrArg _ (K6Kit.cl_rig_tensor' (ε := εt) ((hI j).pow (neg j)).isInvertible_module (hFinv l) _))
      let psb : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) → (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
        fun Ps => pointsSubBasepointModule (a := a) εt Ps
      have hpsbInv : ∀ Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a), Scheme.Modules.IsInvertible (psb Ps) := by
        intro Ps
        induction Ps with
        | nil => exact Scheme.Modules.isInvertible_unit _
        | cons P Ps ih => exact ((hIP P).isInvertible_invModule.tensor hIε.isInvertible_module).tensor ih
      let g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a → K6Kit.Cl a εt (𝟙 (Spec (CommRingCat.of k))) :=
        fun P => K6Kit.clI εt (𝟙 (Spec (CommRingCat.of k))) (RelEffCartierDiv.ofPoint a P.1 P.2).I (hIP P) * E
      have hpsbCl : ∀ Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
          K6Kit.cl (K6Kit.rig εt (𝟙 (Spec (CommRingCat.of k))) (psb Ps) (hpsbInv Ps)) = (Ps.map g).prod := by
        intro Ps
        induction Ps with
        | nil => exact K6Kit.cl_rig_unit' _
        | cons P Ps ih =>
          rw [List.map_cons, List.prod_cons, ← ih]
          exact (K6Kit.cl_rig_tensor' (ε := εt) ((hIP P).isInvertible_invModule.tensor hIε.isInvertible_module) (hpsbInv Ps) _).trans
            (congrArg (· * _) (K6Kit.cl_rig_tensor' (ε := εt) (hIP P).isInvertible_invModule hIε.isInvertible_module _))
      let PsA : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) := (List.finRange m).flatMap fun j => List.replicate (pos j) (Pt j)
      let PsB : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) := (List.finRange m).flatMap fun j => List.replicate (neg j) (Pt j)
      have hsum : (∑ j, pos j) = ∑ j, neg j := by
        have h1 : ((∑ j, pos j : ℕ) : ℤ) = ((∑ j, neg j : ℕ) : ℤ) := by
          rw [Nat.cast_sum, Nat.cast_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]; exact hn
        exact_mod_cast h1
      have hflat : ∀ (n : Fin m → ℕ) (l : List (Fin m)),
          ((l.flatMap fun j => List.replicate (n j) (Pt j)).map g).prod = (l.map fun j => g (Pt j) ^ n j).prod := by
        intro n l
        induction l with
        | nil => rfl
        | cons j l ih =>
          rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_replicate, List.prod_replicate, List.map_cons,
            List.prod_cons]
      have hg : ∀ j, g (Pt j) = Og j * E := fun j => rfl
      have hprodA : (PsA.map g).prod = (∏ j, Og j ^ (pos j)) * E ^ (∑ j, pos j) := by
        show (((List.finRange m).flatMap fun j => List.replicate (pos j) (Pt j)).map g).prod = _
        rw [hflat, ← Fin.prod_univ_def]
        simp only [hg, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      have hprodB : (PsB.map g).prod = (∏ j, Og j ^ (neg j)) * E ^ (∑ j, neg j) := by
        show (((List.finRange m).flatMap fun j => List.replicate (neg j) (Pt j)).map g).prod = _
        rw [hflat, ← Fin.prod_univ_def]
        simp only [hg, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      have key : K6Kit.cl (K6Kit.rig εt (𝟙 (Spec (CommRingCat.of k))) (FoldP (List.finRange m)) (hFinv _)) *
          K6Kit.cl (K6Kit.rig εt (𝟙 (Spec (CommRingCat.of k))) (psb PsB) (hpsbInv PsB)) =
          K6Kit.cl (K6Kit.rig εt (𝟙 (Spec (CommRingCat.of k))) (psb PsA) (hpsbInv PsA)) := by
        rw [hFcl, hpsbCl, hpsbCl, hprodA, hprodB, ← Fin.prod_univ_def, hsum, ← mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [mul_assoc, inv_pow, inv_mul_cancel, mul_one]
      have eFB : Nonempty (FoldP (List.finRange m) ⊗ psb PsB ≅ psb PsA) := by
        rw [← K6Kit.cl_rig_tensor' (ε := εt) (hFinv _) (hpsbInv PsB) ((hFinv _).tensor (hpsbInv PsB))] at key
        exact (K6Kit.cl_eq_iff _ _).1 key

      let LB : XOs.Modules := (Scheme.Modules.pullback (toProdSpec a)).obj (psb PsB)
      have hLB : IsAlgEquivZero a LB :=
        IsAlgEquivZero.of_iso_pointsSubBasepoint εt PsB (fstPullbackToProdSpecPullbackIso a _)
      have hLsB : IsAlgEquivZero a (Ls ⊗ LB) :=
        IsAlgEquivZero.of_iso_pointsSubBasepoint εt PsA
          (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eP.some ⊗ᵢ fstPullbackToProdSpecPullbackIso a _) ≪≫ eFB.some)
      have hLBinv : Scheme.Modules.IsInvertible LB := (hpsbInv PsB).pullback _
      obtain ⟨LB', -, ⟨eLB⟩⟩ := hLBinv.exists_tensor_inverse
      have hLB' : IsAlgEquivZero a LB' := hLB.of_tensor_iso_unit eLB
      exact IsAlgEquivZero.of_iso (α_ _ _ _ ≪≫ whiskerLeftIso Ls eLB ≪≫ ρ_ Ls) (hLsB.tensor hLB')
    ·
      apply hsp
      refine ⟨IsLocalRing.closedPoint k, ?_⟩
      rw [Spec.map_base]
      apply PrimeSpectrum.ext
      let P : Ideal O := Ideal.comap φ (IsLocalRing.maximalIdeal k)
      have hne : P ≠ ⊥ := fun h => hker (by
        rw [RingHom.injective_iff_ker_eq_bot, ← le_bot_iff, ← h]
        exact Ideal.ker_le_comap φ)
      haveI : P.IsPrime := Ideal.comap_isPrime φ _
      have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hne
      exact IsLocalRing.eq_maximalIdeal hmax
  exact ⟨hD.classify tO Mr hF, hD.classify_spec tO Mr hF⟩

end S_ModularCurve_DRResolvedModelPackage_exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_exists_schemeHomOver_poincare_pullbackAlong_iso_of_generic_sectionTwist_of_forall_isAlgEquivZero (solution)
