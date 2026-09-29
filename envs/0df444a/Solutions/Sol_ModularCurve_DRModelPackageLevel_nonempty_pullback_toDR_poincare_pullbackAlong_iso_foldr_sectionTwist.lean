-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8b5c7da1-5641-56be-a96f-fc52049b2a8f

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
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
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_X0MqResolvedTable

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
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve ModularCurve.JZeroNeronObjectAtP"

open IsLocalRing ModularCurve.PlaceSpecialization

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

open Opposite
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace E5W2bHgen
namespace K6a

private theorem isIso_pullback_snd_of_isIso_morphismRestrict {X Y T : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)
    [hU : IsIso (g ∣_ U)] (h : T ⟶ X) (hh : Set.range h.base ⊆ (U : Set X)) : IsIso (pullback.snd g h) := by
  let h' : T ⟶ U := IsOpenImmersion.lift U.ι h (by rwa [Scheme.Opens.range_ι])
  have hh' : h' ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
  have sq := (IsPullback.of_hasPullback (g ∣_ U) h').paste_horiz (isPullback_morphismRestrict g U).flip
  rw [← hh', ← sq.isoPullback_inv_snd]
  infer_instance

private theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

private theorem ringHom_ratSubring_ext (S : Subring ℚ) {K : Type*} [DivisionRing K] [CharZero K] (f g : S →+* K) : f = g := by
  refine RingHom.ext fun x => ?_
  have hden : ((x : ℚ).den : ℚ) ∈ S := natCast_mem S _
  have hnum : ((x : ℚ).num : ℚ) ∈ S := intCast_mem S _
  have hx : x * ⟨_, hden⟩ = ⟨_, hnum⟩ := Subtype.ext (Rat.mul_den_eq_num (x : ℚ))
  have hd : ((x : ℚ).den : K) ≠ 0 := Nat.cast_ne_zero.2 (x : ℚ).den_nz
  have hf : f x * ((x : ℚ).den : K) = ((x : ℚ).num : K) := by
    have := congrArg f hx
    rw [map_mul] at this
    have h1 : f ⟨_, hden⟩ = ((x : ℚ).den : K) := by
      rw [show (⟨_, hden⟩ : S) = ((x : ℚ).den : S) from Subtype.ext (by simp), map_natCast]
    have h2 : f ⟨_, hnum⟩ = ((x : ℚ).num : K) := by
      rw [show (⟨_, hnum⟩ : S) = ((x : ℚ).num : S) from Subtype.ext (by simp), map_intCast]
    rw [h1, h2] at this; exact this
  have hg : g x * ((x : ℚ).den : K) = ((x : ℚ).num : K) := by
    have := congrArg g hx
    rw [map_mul] at this
    have h1 : g ⟨_, hden⟩ = ((x : ℚ).den : K) := by
      rw [show (⟨_, hden⟩ : S) = ((x : ℚ).den : S) from Subtype.ext (by simp), map_natCast]
    have h2 : g ⟨_, hnum⟩ = ((x : ℚ).num : K) := by
      rw [show (⟨_, hnum⟩ : S) = ((x : ℚ).num : S) from Subtype.ext (by simp), map_intCast]
    rw [h1, h2] at this; exact this
  exact mul_right_cancel₀ hd (hf.trans hg.symm)

private theorem ofPoint_I_congr {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (ha : a ≫ f = g) (ha' : a' ≫ f = g) (h : a = a') :
    (RelEffCartierDiv.ofPoint f a ha).I = (RelEffCartierDiv.ofPoint f a' ha').I := by
  subst h; rfl

private def invUnique {X : Scheme.{u}} {L M M' : X.Modules} (e : L ⊗ M ≅ 𝟙_ X.Modules) (e' : L ⊗ M' ≅ 𝟙_ X.Modules) : M ≅ M' :=
  (λ_ M).symm ≪≫ whiskerRightIso (β_ M' L ≪≫ e').symm M ≪≫ α_ M' L M ≪≫ whiskerLeftIso M' e ≪≫ ρ_ M'

private theorem nonempty_pullback_module_iso {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} {J : X'.IdealSheafData}
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

private theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp only [pow_zero]; try exact Scheme.IdealSheafData.comap_top f
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

private theorem smoothRelDimOne_descend {X S S' : Scheme.{u}} (g : X ⟶ S) (f : S' ⟶ S)
    (hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f)
    [SmoothOfRelativeDimension 1 (pullback.fst f g)] : SmoothOfRelativeDimension 1 g :=
  (SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact 1).of_isPullback
    (IsPullback.of_hasPullback f g) hQ ‹_›

private theorem geometricallyIntegral_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [GeometricallyIntegral f] : GeometricallyIntegral g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral e.inv f).mpr ‹_›

private theorem locallyOfFiniteType_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [LocallyOfFiniteType f] : LocallyOfFiniteType g := by
  rw [← he]; infer_instance

private theorem isSeparated_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [IsSeparated f] : IsSeparated g := by
  rw [← he]; infer_instance

end E5W2bHgen.K6a

namespace E5W2bHgen
namespace K6

section ClassGroup

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

variable (c ε) in

private def topGrp : SubPicGroupCondition c ε where
  toSubPicCondition := SubPicCondition.top c ε
  tensor_mem := fun _ _ _ _ _ => trivial
  inv_mem := fun _ _ _ _ _ => trivial

variable (c ε) in

private abbrev Cl {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : Type (u + 1) :=
  (relSubPicPresheaf c ε (topGrp c ε).toSubPicCondition).obj (op (Over.mk t))

private scoped instance instCommGroupCl {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (Cl c ε t) :=
  (topGrp c ε).commGroupObj (op (Over.mk t))

private def cl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) : Cl c ε t :=
  ⟨Quotient.mk _ M, trivial⟩

private theorem cl_eq_iff {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t) :
    cl M = cl N ↔ Nonempty (M.L ≅ N.L) := by
  constructor
  · intro h
    exact Quotient.exact (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Quotient.sound h)

private theorem cl_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {M N : RigidifiedLineBundle c ε t}
    (h : Nonempty (M.L ≅ N.L)) : cl M = cl N :=
  (cl_eq_iff M N).2 h

private theorem cl_tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t) :
    cl (M.tensor N) = cl M * cl N := rfl

private theorem cl_unit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    cl (RigidifiedLineBundle.unit (c := c) (ε := ε) t) = 1 := rfl

private theorem cl_eq_one_of_mul_self {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : Cl c ε t)
    (h : x * x = x) : x = 1 :=
  mul_left_cancel (a := x) (h.trans (mul_one x).symm)

variable {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}

private theorem homEquiv_coe (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (g : Over.mk t ⟶ Over.mk D.toBase) :
    (h.representableBy.homEquiv g).1 = Quotient.mk _ (h.poincare.pullbackAlong ⟨g.left, Over.w g⟩) := rfl

private theorem mul_classify (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
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

private def pcl (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t D.toBase) : Cl c ε t :=
  cl (h.poincare.pullbackAlong x)

private theorem pcl_mul (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
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

private theorem pcl_injective (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {x y : SchemeHomOver t D.toBase} (hxy : pcl h x = pcl h y) : x = y :=
  h.ext_of_iso t x y ((cl_eq_iff _ _).1 hxy)

private def pclHom (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
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

private def rig (L : (pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) : RigidifiedLineBundle c ε t where
  L := L
  isInvertible := hL
  rigidified := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _ (hL.pullback _)

private theorem cl_rig_congr {L M : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (e : Nonempty (L ≅ M)) : cl (rig ε t L hL) = cl (rig ε t M hM) :=
  cl_congr e

private theorem cl_rig_tensor {L M : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) :
    cl (rig ε t (L ⊗ M) (hL.tensor hM)) = cl (rig ε t L hL) * cl (rig ε t M hM) :=
  cl_congr ⟨Iso.refl _⟩

private theorem cl_rig_unit : cl (rig ε t (𝟙_ _) (Scheme.Modules.isInvertible_unit _)) = 1 :=
  cl_congr ⟨Iso.refl _⟩

private theorem cl_rig_L (M : RigidifiedLineBundle c ε t) : cl (rig ε t M.L M.isInvertible) = cl M :=
  cl_congr ⟨Iso.refl _⟩

private theorem cl_rig_tensor' {L M : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (hLM : Scheme.Modules.IsInvertible (L ⊗ M)) :
    cl (rig ε t (L ⊗ M) hLM) = cl (rig ε t L hL) * cl (rig ε t M hM) :=
  cl_congr ⟨Iso.refl _⟩

private theorem cl_rig_unit' (h : Scheme.Modules.IsInvertible (𝟙_ (pullback c t).Modules)) : cl (rig ε t (𝟙_ _) h) = 1 :=
  cl_congr ⟨Iso.refl _⟩

private theorem cl_rig_irrel {L : (pullback c t).Modules} (h h' : Scheme.Modules.IsInvertible L) : cl (rig ε t L h) = cl (rig ε t L h') := rfl

private theorem isInvertible_of_iso {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M) (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  exact ⟨U, hxU, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ eU⟩⟩

variable (ε t) in

private def clI (I : (pullback c t).IdealSheafData) (hI : I.IsInvertible) : Cl c ε t :=
  cl (rig ε t I.invModule hI.isInvertible_invModule)

variable (ε t) in

private def clM (I : (pullback c t).IdealSheafData) (hI : I.IsInvertible) : Cl c ε t :=
  cl (rig ε t I.module hI.isInvertible_module)

private theorem clI_congr {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    clI ε t I hI = clI ε t J hJ := by subst h; rfl

private theorem clM_congr {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    clM ε t I hI = clM ε t J hJ := by subst h; rfl

private theorem clM_mul_clI {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) : clM ε t I hI * clI ε t I hI = 1 := by
  unfold clM clI
  rw [← cl_rig_tensor, ← cl_rig_unit (ε := ε) (t := t)]
  exact cl_congr hI.isInvertible_module.dual.2

private theorem clI_eq_inv {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) : clI ε t I hI = (clM ε t I hI)⁻¹ :=
  eq_inv_of_mul_eq_one_right (clM_mul_clI hI)

private theorem clM_eq_inv {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) : clM ε t I hI = (clI ε t I hI)⁻¹ := by
  rw [clI_eq_inv, inv_inv]

private theorem clI_mul {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (hIJ : (I * J).IsInvertible) :
    clI ε t (I * J) hIJ = clI ε t I hI * clI ε t J hJ := by
  unfold clI
  rw [← cl_rig_tensor]
  exact cl_congr (hI.nonempty_mul_invModule_iso_tensor hJ)

private theorem clM_mul {I J : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (hIJ : (I * J).IsInvertible) :
    clM ε t (I * J) hIJ = clM ε t I hI * clM ε t J hJ := by
  unfold clM
  rw [← cl_rig_tensor]
  exact cl_congr (hI.nonempty_mul_module_iso_tensor hJ)

private theorem clI_one {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) :
    clI ε t 1 (by simpa using hI.pow 0) = 1 := by
  apply cl_eq_one_of_mul_self
  have h1 : (1 : (pullback c t).IdealSheafData).IsInvertible := by simpa using hI.pow 0
  rw [← clI_mul h1 h1 (by simpa using h1)]
  exact clI_congr _ _ (mul_one 1)

private theorem clM_one {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) :
    clM ε t 1 (by simpa using hI.pow 0) = 1 := by
  apply cl_eq_one_of_mul_self
  have h1 : (1 : (pullback c t).IdealSheafData).IsInvertible := by simpa using hI.pow 0
  rw [← clM_mul h1 h1 (by simpa using h1)]
  exact clM_congr _ _ (mul_one 1)

private theorem clI_pow {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    clI ε t (I ^ n) (hI.pow n) = clI ε t I hI ^ n := by
  induction n with
  | zero => rw [pow_zero (clI ε t I hI)]; exact (clI_congr _ _ (pow_zero I)).trans (clI_one hI)
  | succ n ih =>
    rw [pow_succ (clI ε t I hI) n, ← ih]
    have hJ : (I ^ n * I).IsInvertible := by rw [← pow_succ]; exact hI.pow (n + 1)
    exact (clI_congr _ hJ (pow_succ I n)).trans (clI_mul (hI.pow n) hI hJ)

private theorem clM_pow {I : (pullback c t).IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    clM ε t (I ^ n) (hI.pow n) = clM ε t I hI ^ n := by
  induction n with
  | zero => rw [pow_zero (clM ε t I hI)]; exact (clM_congr _ _ (pow_zero I)).trans (clM_one hI)
  | succ n ih =>
    rw [pow_succ (clM ε t I hI) n, ← ih]
    have hJ : (I ^ n * I).IsInvertible := by rw [← pow_succ]; exact hI.pow (n + 1)
    exact (clM_congr _ hJ (pow_succ I n)).trans (clM_mul (hI.pow n) hI hJ)

end Rig

end E5W2bHgen.K6
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen"

namespace E5W2bHgen
namespace K6

private theorem _root_.E5W2bHgen.K6.smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

p2m_export "E5W2bHgen.K6" "smoothOfRelativeDimension_one_of_iso"

set_option maxHeartbeats 1600000 in
private theorem poincare_ajK
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)
    [IsProper (DRLevel.toBase N₀ p)]
    (h' : RepresentsRelSubPic (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
          (algEquivZeroCut (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRLevel.toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), pullback.condition⟩)).L))
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (Qb : Type) [Field Qb] (sQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ℚ))
    (xQ : SchemeHomOver sQ (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ))
    [SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase N₀ p) (sQ ≫ specMap (DRLevel.R p) ℚ))]
    (hw : (xQ.1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ)) ≫ D.toBase = sQ ≫ specMap (DRLevel.R p) ℚ)
    (hxw : (xQ.1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) ≫ DRLevel.toBase N₀ p = sQ ≫ specMap (DRLevel.R p) ℚ)
    (hε : ((sQ ≫ specMap (DRLevel.R p) ℚ) ≫ 𝔓.εinf.1) ≫ DRLevel.toBase N₀ p = sQ ≫ specMap (DRLevel.R p) ℚ) :
    Nonempty ((hD.poincare.pullbackAlong ⟨xQ.1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), hw⟩).L ≅
      (RelEffCartierDiv.ofPoint (DRLevel.toBase N₀ p) (xQ.1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) hxw).lineBundle ⊗
      (RelEffCartierDiv.ofPoint (DRLevel.toBase N₀ p) ((sQ ≫ specMap (DRLevel.R p) ℚ) ≫ 𝔓.εinf.1) hε).idealModule) := by

  let c := DRLevel.toBase N₀ p
  let c' := baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of (DRLevel.R p)) := sQ ≫ specMap (DRLevel.R p) ℚ
  have hsX : tQ = sQ ≫ specMap (DRLevel.R p) ℚ := rfl
  let y : Spec (CommRingCat.of Qb) ⟶ pullback (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ) := xQ.1
  have hy : y ≫ c' = sQ := xQ.2
  obtain ⟨i2⟩ := hajQ Qb sQ xQ

  let κ' : pullback c' sQ ≅ pullback c tQ := BaseChange.κ c ℚ sQ ≪≫ pullback.congrHom rfl hsX.symm
  have hκ'1 : κ'.hom ≫ pullback.fst c tQ = pullback.fst c' sQ ≫ pullback.fst c (specMap (DRLevel.R p) ℚ) := by
    simp only [κ', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
    exact BaseChange.κ_hom_fst c ℚ sQ
  have hκ'2 : κ'.hom ≫ pullback.snd c tQ = pullback.snd c' sQ := by
    simp only [κ', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
    exact BaseChange.κ_hom_snd c ℚ sQ

  let tD' := (D.baseChange ℚ).toBase
  let φD : SchemeHomOver (tD' ≫ specMap (DRLevel.R p) ℚ) D.toBase := ⟨pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), pullback.condition⟩
  let ψ : SchemeHomOver sQ tD' := ⟨xQ.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (xQ.1 ≫ ·) ajQ.2).trans xQ.2)⟩
  let g : SchemeHomOver tQ D.toBase := ⟨xQ.1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), hw⟩
  have E : (baseChangeSnd c' ψ ≫ (BaseChange.κ c ℚ tD').hom) ≫ baseChangeSnd c φD = κ'.hom ≫ baseChangeSnd c g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, ← Category.assoc,
        BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst', hκ'1]
    · show ((baseChangeSnd c' ψ ≫ (BaseChange.κ c ℚ tD').hom) ≫ baseChangeSnd c φD) ≫ pullback.snd c D.toBase =
        (κ'.hom ≫ baseChangeSnd c g) ≫ pullback.snd c D.toBase
      simp only [Category.assoc, BaseChange.baseChangeSnd_snd']
      rw [reassoc_of% (BaseChange.κ_hom_snd c ℚ tD'), reassoc_of% (BaseChange.baseChangeSnd_snd' ℚ c' ψ), reassoc_of% hκ'2]
      show pullback.snd c' sQ ≫ (xQ.1 ≫ ajQ.1) ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ) =
        pullback.snd c' sQ ≫ xQ.1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ)
      simp only [Category.assoc]
  let P := hD.poincare.L
  have i1 : (h'.poincare.pullbackAlong ψ).L ≅ (Scheme.Modules.pullback κ'.hom).obj ((hD.poincare.pullbackAlong g).L) :=
    (Scheme.Modules.pullback (baseChangeSnd c' ψ)).mapIso hP.some ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd c' ψ) (BaseChange.κ c ℚ tD').hom).app
        ((Scheme.Modules.pullback (baseChangeSnd c φD)).obj P) ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd c' ψ ≫ (BaseChange.κ c ℚ tD').hom) (baseChangeSnd c φD)).app P ≪≫
      (Scheme.Modules.pullbackCongr E).app P ≪≫
      ((Scheme.Modules.pullbackComp κ'.hom (baseChangeSnd c g)).app P).symm

  have i3 : (hD.poincare.pullbackAlong g).L ≅ (Scheme.Modules.pullback κ'.inv).obj ((h'.poincare.pullbackAlong ψ).L) :=
    ((Scheme.Modules.pullbackId _).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr κ'.inv_hom_id.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp κ'.inv κ'.hom).app _).symm ≪≫
      (Scheme.Modules.pullback κ'.inv).mapIso i1.symm
  have i4 := i3 ≪≫ (Scheme.Modules.pullback κ'.inv).mapIso i2 ≪≫ Scheme.Modules.pullbackTensorObjIso κ'.inv _ _

  have hp : graphOver c (xQ.1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) hxw ≫ κ'.inv = graphOver c' y hy := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, hκ'1, graphOver_fst_assoc, graphOver_fst]
    · rw [Category.assoc, hκ'2, graphOver_snd, graphOver_snd]
  have hpε : graphOver c (tQ ≫ 𝔓.εinf.1) hε ≫ κ'.inv =
      graphOver c' (sQ ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (sQ ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans (Category.comp_id sQ))) := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc (graphOver c' _ _) κ'.hom (pullback.fst c tQ), hκ'1, graphOver_fst_assoc]
      rw [Category.assoc sQ _ (pullback.fst c (specMap (DRLevel.R p) ℚ)), sectionBaseChange_coe_fst]
      simp only [tQ, Category.assoc]
    · rw [graphOver_snd, Category.assoc (graphOver c' _ _) κ'.hom (pullback.snd c tQ), hκ'2, graphOver_snd]

  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd c tQ) := ‹_›
  haveI hsm' : SmoothOfRelativeDimension 1 (pullback.snd c' sQ) :=
    smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tQ) κ'.symm hκ'2
  have j := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso κ'.inv _ _ hp
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' sQ) _ (graphOver_snd _ _ _))
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tQ) _ (graphOver_snd _ _ _)) 1
  have jε := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso κ'.inv _ _ hpε
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' sQ) _ (graphOver_snd _ _ _))
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tQ) _ (graphOver_snd _ _ _)) 1
  simp only [pow_one] at j jε
  obtain ⟨⟨j1⟩, -⟩ := j
  obtain ⟨-, ⟨j2⟩⟩ := jε
  exact ⟨i4 ≪≫ (j1 ⊗ᵢ j2)⟩

set_option maxHeartbeats 3200000 in
private theorem nonempty_poincare_iso_foldr_of_eq_prod_zpow
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)
    [IsProper (DRLevel.toBase N₀ p)]
    (h' : RepresentsRelSubPic (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
          (algEquivZeroCut (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRLevel.toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), pullback.condition⟩)).L))
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (F : Type) [Field F] (sF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of ℚ))
    [SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase N₀ p) (sF ≫ specMap (DRLevel.R p) ℚ))]
    (zF : SchemeHomOver (sF ≫ specMap (DRLevel.R p) ℚ) D.toBase)
    (m : ℕ) (xF : Fin m → SchemeHomOver sF (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ)) (pos neg : Fin m → ℕ)
    (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (hw : ∀ j, ((xF j).1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ)) ≫ D.toBase = sF ≫ specMap (DRLevel.R p) ℚ)
    (hzF : letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRLevel.toBase N₀ p) 𝔓.εinf) hD).pointGroup (sF ≫ specMap (DRLevel.R p) ℚ)
      zF = ((List.finRange m).map fun j =>
        (⟨(xF j).1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), hw j⟩ : SchemeHomOver (sF ≫ specMap (DRLevel.R p) ℚ) D.toBase) ^
          ((pos j : ℤ) - (neg j : ℤ))).prod)
    (hx : ∀ j, ((xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) ≫ DRLevel.toBase N₀ p = sF ≫ specMap (DRLevel.R p) ℚ) :
    Nonempty ((hD.poincare.pullbackAlong zF).L ≅
      (List.finRange m).foldr (fun j M =>
          ((RelEffCartierDiv.ofPoint (DRLevel.toBase N₀ p) ((xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) (hx j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRLevel.toBase N₀ p) ((xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) (hx j)).I ^ (neg j)).module ⊗ M)
        (𝟙_ (pullback (DRLevel.toBase N₀ p) (sF ≫ specMap (DRLevel.R p) ℚ)).Modules)) := by
  classical
  let c := DRLevel.toBase N₀ p
  let ε := 𝔓.εinf
  let tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (DRLevel.R p)) := sF ≫ specMap (DRLevel.R p) ℚ
  let Pg := algEquivZeroGroupCut c ε
  letI := (RepresentsRelSubPic.relativeGroupLaw (P := Pg) hD).pointGroup tF
  have hε : (tF ≫ ε.1) ≫ c = tF := (Category.assoc _ _ _).trans ((congrArg (tF ≫ ·) ε.2).trans (Category.comp_id _))
  let I : Fin m → (pullback c tF).IdealSheafData := fun j =>
    (RelEffCartierDiv.ofPoint c ((xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) (hx j)).I
  let Iε : (pullback c tF).IdealSheafData := (RelEffCartierDiv.ofPoint c (tF ≫ ε.1) hε).I
  have hI : ∀ j, (I j).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tF) _ (graphOver_snd _ _ _)
  have hIε : Iε.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tF) _ (graphOver_snd _ _ _)
  let Og : Fin m → Cl c ε tF := fun j => clI ε tF (I j) (hI j)
  let E : Cl c ε tF := clM ε tF Iε hIε
  let a : Fin m → SchemeHomOver tF D.toBase := fun j => ⟨(xF j).1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), hw j⟩

  have step1 : ∀ j, pcl (P := Pg) hD (a j) = Og j * E := by
    intro j
    unfold pcl
    rw [← cl_rig_L]
    have hF := poincare_ajK N₀ p hpN₀ 𝔓 D hD h' ajQ hP hajQ F sF (xF j) (hw j) (hx j) hε
    exact (cl_rig_congr (ε := ε) _ ((hI j).isInvertible_invModule.tensor hIε.isInvertible_module) hF).trans
      (cl_rig_tensor (ε := ε) _ _)

  have hEsum : ∀ s : Finset (Fin m), ∏ j ∈ s, E ^ ((pos j : ℤ) - (neg j : ℤ)) = E ^ (∑ j ∈ s, ((pos j : ℤ) - (neg j : ℤ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]
  have hL : pcl (P := Pg) hD zF = ∏ j, Og j ^ ((pos j : ℤ) - (neg j : ℤ)) := by
    have e0 : pcl (P := Pg) hD zF = pclHom (P := Pg) hD tF zF := rfl
    have h2 : ∀ j, pclHom (P := Pg) hD tF (a j) = Og j * E := step1
    rw [e0, hzF, map_list_prod, List.map_map, ← Fin.prod_univ_def]
    rw [show (∏ j, ((pclHom (P := Pg) hD tF) ∘ fun j => a j ^ ((pos j : ℤ) - (neg j : ℤ))) j) = ∏ j, (Og j * E) ^ ((pos j : ℤ) - (neg j : ℤ)) from
      Finset.prod_congr rfl fun j _ => by simp only [Function.comp, map_zpow, h2]]
    simp only [mul_zpow, Finset.prod_mul_distrib, hEsum, hn, zpow_zero, mul_one]

  let Fo : Fin m → (pullback c tF).Modules → (pullback c tF).Modules := fun j M =>
    ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module ⊗ M
  have hFinv : ∀ l : List (Fin m), Scheme.Modules.IsInvertible (l.foldr Fo (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact Scheme.Modules.isInvertible_unit _
    | cons j l ih => exact ((hI j).pow (pos j)).isInvertible_invModule.tensor (((hI j).pow (neg j)).isInvertible_module.tensor ih)
  have hFcl : ∀ l : List (Fin m), cl (rig ε tF (l.foldr Fo (𝟙_ _)) (hFinv l)) =
      (l.map fun j => clI ε tF ((I j) ^ (pos j)) ((hI j).pow _) * clM ε tF ((I j) ^ (neg j)) ((hI j).pow _)).prod := by
    intro l
    induction l with
    | nil => exact cl_rig_unit' _
    | cons j l ih =>
      rw [List.map_cons, List.prod_cons, ← ih, mul_assoc]
      exact (cl_rig_tensor' (ε := ε) ((hI j).pow (pos j)).isInvertible_invModule
          (((hI j).pow (neg j)).isInvertible_module.tensor (hFinv l)) _).trans
        (congrArg _ (cl_rig_tensor' (ε := ε) ((hI j).pow (neg j)).isInvertible_module (hFinv l) _))
  have hFold : cl (rig ε tF ((List.finRange m).foldr Fo (𝟙_ _)) (hFinv _)) = ∏ j, Og j ^ ((pos j : ℤ) - (neg j : ℤ)) := by
    rw [hFcl, ← Fin.prod_univ_def]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [clI_pow (hI j), clM_pow (hI j), clM_eq_inv (hI j)]
    show Og j ^ pos j * (Og j)⁻¹ ^ neg j = Og j ^ ((pos j : ℤ) - (neg j : ℤ))
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add, sub_eq_add_neg]
  have hPz : cl (rig ε tF (hD.poincare.pullbackAlong zF).L (hD.poincare.pullbackAlong zF).isInvertible) =
      cl (rig ε tF ((List.finRange m).foldr Fo (𝟙_ _)) (hFinv _)) := by
    rw [hFold, ← hL]
    exact cl_rig_L _
  exact (cl_eq_iff _ _).1 hPz

end E5W2bHgen.K6
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"

namespace E5W2bHgen
namespace K5
open E5W2bHgen.K6a
set_option maxHeartbeats 3200000 in

private theorem genTransportInv
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [IsProper (DRLevel.toBase N₀ p)] (O : Type) [CommRing O] [IsDomain O] (ρO : DRLevel.R p →+* O)
    (hpO : ((p : ℕ) : O) ≠ 0)
    (Y : Scheme.{0}) (toBase : Y ⟶ Spec (CommRingCat.of O))
    (toDR : Y ⟶ pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)))
    (toDR_over : toDR ≫ pullback.snd _ _ = toBase) [IsProper toBase]
    (toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRLevel.toBase N₀ p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))))
    (M : (pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO))).Modules)
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) toBase) (pos neg : Fin m → ℕ)
    (K : Type) [Field K] (τ : O →+* K) (hτp : τ (p : O) ≠ 0)
    (tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (DRLevel.R p)))
    (htK : Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom ρO) = tK)
    [SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase N₀ p) tK)]
    (hx : ∀ j, ((Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) ≫ DRLevel.toBase N₀ p = tK)
    (hM : Nonempty ((Scheme.Modules.pullback (baseChangeSnd (DRLevel.toBase N₀ p)
        (⟨Spec.map (CommRingCat.ofHom τ), htK⟩ : SchemeHomOver tK (Spec.map (CommRingCat.ofHom ρO))))).obj M ≅
      (List.finRange m).foldr (fun j N =>
          ((RelEffCartierDiv.ofPoint (DRLevel.toBase N₀ p) ((Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _)
              (hx j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRLevel.toBase N₀ p) ((Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _)
              (hx j)).I ^ (neg j)).module ⊗ N)
        (𝟙_ (pullback (DRLevel.toBase N₀ p) tK).Modules))) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst toBase (Spec.map (CommRingCat.ofHom τ)) ≫ toDR)).obj M ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist toBase (σ j) (Spec.map (CommRingCat.ofHom τ)) (pos j) ⊗
              ((sectionIdeal toBase (σ j) (Spec.map (CommRingCat.ofHom τ))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback toBase (Spec.map (CommRingCat.ofHom τ))).Modules)) := by
  subst toDR_over
  obtain ⟨hM⟩ := hM

  let c := DRLevel.toBase N₀ p
  let tO : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of (DRLevel.R p)) := Spec.map (CommRingCat.ofHom ρO)
  let c' := toDR ≫ pullback.snd c tO
  let tb : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom τ)
  have htb : tb ≫ tO = tK := htK

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
      (t' : T ⟶ Spec (CommRingCat.of (DRLevel.R p))) (htt : t ≫ tO = t'),
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
    haveI : IsIso (pullback.snd toDR h) := E5W2bHgen.K6a.isIso_pullback_snd_of_isIso_morphismRestrict toDR _ h hh
    let e2 : pullback c' t ≅ pullback toDR h := (pullbackRightPullbackFstIso (pullback.snd c tO) t toDR).symm
    let e4 : pullback toDR h ≅ pullback (pullback.snd c tO) t := asIso (pullback.snd toDR h)
    let e5 : pullback (pullback.snd c tO) t ≅ pullback c (t ≫ tO) := pullbackLeftPullbackSndIso c tO t
    refine ⟨e2 ≪≫ e4 ≪≫ e5, ?_, ?_⟩
    · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, asIso_hom,
        Iso.symm_hom, pullbackRightPullbackFstIso_inv_snd_snd]
    · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, asIso_hom,
        ← pullback.condition_assoc, Iso.symm_hom, pullbackRightPullbackFstIso_inv_fst_assoc]
  obtain ⟨eY, heY1, heY2⟩ := mkIso tb (hmemU τ hτp) tK htb
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c' tb) :=
    E5W2bHgen.K6a.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tK) eY.symm heY1

  have hIb : ∀ j, (sectionIdeal c' (σ j) tb).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' tb) _ (pullback.lift_snd _ _ _)
  have hIX : ∀ j, (RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) (hx j)).I.IsInvertible :=
    fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tK) _ (graphOver_snd _ _ _)

  let ψb : SchemeHomOver tK tO := ⟨tb, htb⟩
  let bO := baseChangeSnd c ψb
  have heYbO : eY.hom ≫ bO = pullback.fst c' tb ≫ toDR := by
    apply pullback.hom_ext
    · rw [Category.assoc, BaseChange.baseChangeSnd_fst', heY2, Category.assoc]
    · rw [Category.assoc, BaseChange.baseChangeSnd_snd', reassoc_of% heY1, Category.assoc, pullback.condition]

  have hσb : ∀ j, (tb ≫ (σ j).1) ≫ c' = tb := fun j => by rw [Category.assoc, (σ j).2, Category.comp_id]
  have hgraph : ∀ j, graphOver c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) (hx j) ≫ eY.inv =
      graphOver c' (tb ≫ (σ j).1) (hσb j) := by
    intro j
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc (graphOver c' _ _) eY.hom (pullback.fst c tK), heY2, graphOver_fst_assoc]
    · rw [graphOver_snd, Category.assoc (graphOver c' _ _) eY.hom (pullback.snd c tK), heY1, graphOver_snd]
  have jX : ∀ j (n : ℕ),
      Nonempty ((Scheme.Modules.pullback eY.inv).obj (((sectionIdeal c' (σ j) tb) ^ n).invModule) ≅
        ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) (hx j)).I ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback eY.inv).obj (((sectionIdeal c' (σ j) tb) ^ n).module) ≅
        ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) (hx j)).I ^ n).module) :=
    fun j n => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso eY.inv _ _ (hgraph j) (hIb j) (hIX j) n
  have PD : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback eY.inv).obj (l.foldr
        (fun j N => (sectionTwist c' (σ j) tb (pos j) ⊗ ((sectionIdeal c' (σ j) tb) ^ (neg j)).module) ⊗ N) (𝟙_ _)) ≅
      l.foldr (fun j N =>
          ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) (hx j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint c ((tb ≫ (σ j).1) ≫ toDR ≫ pullback.fst (DRLevel.toBase N₀ p) _) (hx j)).I ^ (neg j)).module ⊗ N)
        (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact ⟨Scheme.Modules.pullbackTensorUnitObjIso eY.inv⟩
    | cons j l ih =>
      exact ⟨Scheme.Modules.pullbackTensorObjIso eY.inv _ _ ≪≫
        ((Scheme.Modules.pullbackTensorObjIso eY.inv _ _ ≪≫ ((jX j (pos j)).1.some ⊗ᵢ (jX j (neg j)).2.some)) ⊗ᵢ ih.some) ≪≫
        α_ _ _ _⟩
  obtain ⟨pd⟩ := PD (List.finRange m)
  exact ⟨(Scheme.Modules.pullbackCongr heYbO.symm).app M ≪≫ ((Scheme.Modules.pullbackComp eY.hom bO).app M).symm ≪≫
    (Scheme.Modules.pullback eY.hom).mapIso (hM ≪≫ pd.symm) ≪≫
    (Scheme.Modules.pullbackComp eY.hom eY.inv).app _ ≪≫ (Scheme.Modules.pullbackCongr eY.hom_inv_id).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _⟩

end E5W2bHgen.K5
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"

private theorem E5W2bHgen.eq_of_specMap_comp_eq_specMap_comp
    {F L : Type u} [Field F] [Field L] (i : F →+* L) {X : Scheme.{u}} (a b : Spec (CommRingCat.of F) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ a = Spec.map (CommRingCat.ofHom i) ≫ b) : a = b := by

  let pt : X := a.base (IsLocalRing.closedPoint F)
  have hpta : ∀ y : Spec (CommRingCat.of F), a.base y = pt := fun y => by
    rw [show y = IsLocalRing.closedPoint F from Subsingleton.elim _ _]
  have hptb : ∀ y : Spec (CommRingCat.of F), b.base y = pt := fun y => by
    rw [show y = IsLocalRing.closedPoint F from Subsingleton.elim _ _]
    have := congrArg (fun f : Spec (CommRingCat.of L) ⟶ X => f.base (IsLocalRing.closedPoint L)) h
    have ea : (Spec.map (CommRingCat.ofHom i) ≫ a).base (IsLocalRing.closedPoint L) =
        a.base ((Spec.map (CommRingCat.ofHom i)).base (IsLocalRing.closedPoint L)) := rfl
    have eb : (Spec.map (CommRingCat.ofHom i) ≫ b).base (IsLocalRing.closedPoint L) =
        b.base ((Spec.map (CommRingCat.ofHom i)).base (IsLocalRing.closedPoint L)) := rfl
    simp only [ea, eb] at this
    rw [show (Spec.map (CommRingCat.ofHom i)).base (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint F from
      Subsingleton.elim _ _] at this
    exact this.symm
  obtain ⟨_, ⟨U', hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ pt) isOpen_univ
  let U : X.Opens := U'
  have hU : IsAffineOpen U := hU
  have hra : Set.range a.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨y, rfl⟩; rw [hpta]; exact hpt
  have hrb : Set.range b.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨y, rfl⟩; rw [hptb]; exact hpt
  let a' := IsOpenImmersion.lift U.ι a hra
  let b' := IsOpenImmersion.lift U.ι b hrb
  have ha' : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hb' : b' ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h' : Spec.map (CommRingCat.ofHom i) ≫ a' = Spec.map (CommRingCat.ofHom i) ≫ b' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ha', hb', h]

  let φa : Γ(X, U) ⟶ CommRingCat.of F := Spec.preimage (a' ≫ hU.isoSpec.hom)
  let φb : Γ(X, U) ⟶ CommRingCat.of F := Spec.preimage (b' ≫ hU.isoSpec.hom)
  have hφ : φa ≫ CommRingCat.ofHom i = φb ≫ CommRingCat.ofHom i := by
    apply Spec.map_inj.1
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, reassoc_of% h']
  have hφ' : φa = φb := by
    ext r
    apply i.injective
    exact congrArg (fun ψ : Γ(X, U) ⟶ CommRingCat.of L => ψ.hom r) hφ
  have : a' = b' := by
    rw [← cancel_mono hU.isoSpec.hom, ← Spec.map_preimage (a' ≫ hU.isoSpec.hom), ← Spec.map_preimage (b' ≫ hU.isoSpec.hom)]
    exact congrArg Spec.map hφ'
  rw [← ha', ← hb', this]

namespace E5W2bHgen
namespace K6

private theorem schemeHomOver_eq_prod_zpow_of_comp_eq_pts
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)
    (pts : JZero (N₀ * p) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero (N₀ * p), pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRLevel.toBase N₀ p) 𝔓.εinf) hD).mul _ (pts x) (pts y))
    {F : Type} [Field F] (tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (DRLevel.R p)))
    (r : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of F))
    (hr : r ≫ tF = Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))))
    (hrmap : ∃ i : F →+* AlgebraicClosure ℚ, r = Spec.map (CommRingCat.ofHom i))
    (zF : SchemeHomOver tF D.toBase) {m : ℕ} (a : Fin m → SchemeHomOver tF D.toBase) (n : Fin m → ℤ)
    (xz : JZero (N₀ * p)) (xa : Fin m → JZero (N₀ * p))
    (hz : schemeHomOverComp r hr zF = pts xz)
    (ha : ∀ j, schemeHomOverComp r hr (a j) = pts (xa j))
    (hsum : xz = ∑ j, n j • xa j) :
    letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRLevel.toBase N₀ p) 𝔓.εinf) hD).pointGroup tF
    zF = ((List.finRange m).map fun j => (a j) ^ (n j)).prod := by
  set G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRLevel.toBase N₀ p) 𝔓.εinf) hD with hG
  letI instF := G.pointGroup tF
  letI instQ := G.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))))

  let ρ : SchemeHomOver tF D.toBase →* SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) D.toBase :=
    MonoidHom.mk' (schemeHomOverComp r hr) (fun x y => G.mul_natural tF _ r hr x y)
  have hρ : ∀ x, ρ x = schemeHomOverComp r hr x := fun _ => rfl

  let Φ : JZero (N₀ * p) →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) D.toBase) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pts x)) (fun x y => by
      show Additive.ofMul (pts (x + y)) = Additive.ofMul (pts x) + Additive.ofMul (pts y)
      rw [pts_add]; rfl)
  have hΦ : ∀ x, Additive.toMul (Φ x) = pts x := fun _ => rfl

  have hQ : ρ zF = ρ (((List.finRange m).map fun j => (a j) ^ (n j)).prod) := by
    have lhs : ρ zF = pts xz := by rw [hρ, hz]
    have rhs : ρ (((List.finRange m).map fun j => (a j) ^ (n j)).prod) =
        ((List.finRange m).map fun j => (pts (xa j)) ^ (n j)).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      show ρ ((a j) ^ (n j)) = (pts (xa j)) ^ (n j)
      rw [map_zpow, hρ, ha]
    have mid : pts xz = ((List.finRange m).map fun j => (pts (xa j)) ^ (n j)).prod := by
      rw [← hΦ, hsum, Fin.sum_univ_def, map_list_sum, List.map_map, toMul_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      show Additive.toMul (Φ (n j • xa j)) = (pts (xa j)) ^ (n j)
      rw [map_zsmul, toMul_zsmul, hΦ]
    rw [lhs, mid, rhs]

  obtain ⟨i, rfl⟩ := hrmap
  apply Subtype.ext
  have h1 := congrArg Subtype.val hQ
  rw [hρ, hρ, GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe] at h1
  exact E5W2bHgen.eq_of_specMap_comp_eq_specMap_comp i _ _ h1

end E5W2bHgen.K6
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"

namespace E5W2bHgen
namespace K6

private theorem degree_eq_sum (M : ℕ) [NeZero M] (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, ModularCurve.deg_eq_one_modularFunctionFieldBar M v, Nat.cast_one, mul_one]

private theorem mapDomain_mem_degZero {M M' : ℕ} [NeZero M] [NeZero M']
    (e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'))
    (D : ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(modularFunctionFieldBar M)))) :
    Finsupp.mapDomain e (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) ∈
      Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(modularFunctionFieldBar M')) := by
  rw [Divisor.mem_degZero, degree_eq_sum, Finsupp.sum_mapDomain_index_inj e.injective, ← degree_eq_sum]
  exact D.2

private noncomputable def mkHom (M : ℕ) [NeZero M] : ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(modularFunctionFieldBar M))) →+ JZero M where
  toFun := Pic0.mk
  map_zero' := Pic0.mk_zero
  map_add' := Pic0.mk_add

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem pic0Mk_eq_sum_zsmul
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (D₀ : ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (m : ℕ) (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support))
    (pos neg : Fin m → ℕ)
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
      (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))))
    (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (Dv : Fin m → ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (hDv : ∀ j, (Dv j : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      Finsupp.single (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1) :
    Pic0.mk D₀ = ∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Pic0.mk (Dv j) := by

  have hsum : (∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Pic0.mk (Dv j) : JZero (N₀ * p)) =
      mkHom (N₀ * p) (∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Dv j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul]; rfl
  rw [hsum]
  show mkHom (N₀ * p) D₀ = mkHom (N₀ * p) _
  congr 1
  apply Subtype.ext

  rw [AddSubgroup.val_finsetSum]
  simp only [AddSubgroupClass.coe_zsmul, hDv, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hn, zero_smul,
    sub_zero]

  show (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
    ∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Finsupp.single (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) 1
  conv_lhs => rw [← Finsupp.sum_single (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p)))]
  rw [Finsupp.sum, ← Finset.sum_coe_sort, ← Equiv.sum_comp idx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hmult j, Finsupp.smul_single', mul_one]

end E5W2bHgen.K6
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist.E5W2bHgen.K6"

private theorem E5W2bHgen.hom_spec_rat_ext (K : Type) [Field K] [CharZero K]
    (f g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry in

private theorem E5W2bHgen.K6a.foldr_ofPoint_congr {𝒞 S T : Scheme.{0}} (f : 𝒞 ⟶ S) [IsSeparated f] (g : T ⟶ S) {m : ℕ}
    (a a' : Fin m → (T ⟶ 𝒞)) (ha : ∀ j, a j ≫ f = g) (ha' : ∀ j, a' j ≫ f = g) (h : a = a') (pos neg : Fin m → ℕ) :
    Nonempty ((List.finRange m).foldr
        (fun j M => ((RelEffCartierDiv.ofPoint f (a j) (ha j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint f (a j) (ha j)).I ^ (neg j)).module ⊗ M) (𝟙_ (pullback f g).Modules) ≅
      (List.finRange m).foldr
        (fun j M => ((RelEffCartierDiv.ofPoint f (a' j) (ha' j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint f (a' j) (ha' j)).I ^ (neg j)).module ⊗ M) (𝟙_ (pullback f g).Modules)) := by
  subst h; exact ⟨Iso.refl _⟩

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution

    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)}

    (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    [IsProper (DRLevel.toBase N₀ p)]
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (DRLevel.toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (kQ : pullback (DRLevel.toBase N₀ p) (genPt p) ⟶ pullback (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ) = pullback.fst (DRLevel.toBase N₀ p) (genPt p))
    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ))
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1)
    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (ρO : DRLevel.R p →+* O)
    {k : Type} [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO k toκ)

    (x : ↥(inertiaInvariants A (N₀ * p)))
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (hD₀ : Pic0.mk D₀ = (x : JZero (N₀ * p)))

    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase)
    (hz : Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ z.1 = (pts (x : JZero (N₀ * p))).1)

    (m : ℕ) (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))).support))
    (pos neg : Fin m → ℕ)
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
      (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))))
    (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)

    (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (hσgen : ∀ j, Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ (σ j).1 ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) =
      ((𝔓.Meta.pointEquivPlace).symm (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) _) :
    Nonempty (
        (Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj
            ((Scheme.Modules.pullback 𝔛reg.toDR).obj (hD.poincare.pullbackAlong z).L) ≅
          (List.finRange m).foldr
            (fun j M => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))) (pos j) ⊗
                ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))) ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))).Modules)) := by
  classical
  haveI := 𝔓.eeta_iso

  let τ : O →+* (AlgebraicClosure ℚ) := (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).subtype.comp eO.toRingHom)
  have hτinj : Function.Injective τ :=
    (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).injective.comp (Subtype.val_injective.comp eO.injective)
  let F := FractionRing O
  let τF : F →+* (AlgebraicClosure ℚ) := IsFractionRing.lift hτinj
  have hτ : τF.comp (algebraMap O F) = τ := IsLocalization.lift_comp _
  haveI : CharZero F := τF.charZero
  let sF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of ℚ) := Spec.map (CommRingCat.ofHom (algebraMap ℚ F))
  let tb : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O F))
  let tK : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (DRLevel.R p)) := sF ≫ specMap (DRLevel.R p) ℚ
  let r : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom τF)
  have htK : tb ≫ (Spec.map (CommRingCat.ofHom ρO)) = tK := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2; try exact E5W2bHgen.K6a.ringHom_ratSubring_ext _ _ _
  have hrtb : r ≫ tb = Spec.map (CommRingCat.ofHom τ) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]
  have hr : r ≫ tK = (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) := by
    rw [← htK, reassoc_of% hrtb]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; try exact E5W2bHgen.K6a.ringHom_ratSubring_ext _ _ _

  have hpO : ((p : ℕ) : O) ≠ 0 := fun h =>
    IsDiscreteValuationRing.not_a_field O (by rw [hϖO]; exact Ideal.span_singleton_eq_bot.2 h)
  have hτp : algebraMap O F (p : O) ≠ 0 := fun h =>
    hpO ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective O F) _ h)

  haveI hsm0 : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) :=
    𝔓.smooth_generic
  haveI hsmK : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase N₀ p) tK) :=
    E5W2bHgen.K6a.smoothOfRelativeDimension_one_of_iso (f := pullback.snd (pullback.snd (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) sF)
      (pullbackLeftPullbackSndIso (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ) sF) (by rw [Iso.inv_comp_eq]; exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm)

  let q : Fin m → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} := fun j =>
    (𝔓.Meta.pointEquivPlace).symm (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
  have hxpt : ∀ j, ((tb ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO))) ≫ DRLevel.toBase N₀ p = sF ≫ specMap (DRLevel.R p) ℚ := fun j => by
    rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛reg.toDR_over, reassoc_of% (σ j).2]
    exact htK
  let xF : Fin m → SchemeHomOver sF (baseChange (DRLevel.R p) (DRLevel.toBase N₀ p) ℚ) := fun j =>
    ⟨pullback.lift ((tb ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO))) sF (hxpt j), pullback.lift_snd _ _ _⟩
  have hxF1 : ∀ j, (xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ) = (tb ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)) :=
    fun j => pullback.lift_fst _ _ _

  have hxq : ∀ j, r ≫ (xF j).1 = (q j).1 ≫ 𝔓.eeta ≫ kQ := by
    intro j
    apply pullback.hom_ext
    · rw [Category.assoc, hxF1]
      simp only [Category.assoc]
      rw [reassoc_of% hrtb, hkQ₁]
      exact hσgen j
    · exact E5W2bHgen.hom_spec_rat_ext (AlgebraicClosure ℚ) _ _

  have hw : ∀ j, ((xF j).1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ)) ≫ D.toBase = tK := fun j => by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ajQ.1]
    show (xF j).1 ≫ (ajQ.1 ≫ (D.baseChange ℚ).toBase) ≫ specMap (DRLevel.R p) ℚ = tK
    rw [ajQ.2, reassoc_of% (xF j).2]
  let a : Fin m → SchemeHomOver tK D.toBase := fun j => ⟨(xF j).1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ), hw j⟩
  let zF : SchemeHomOver tK D.toBase := ⟨tb ≫ z.1, by rw [Category.assoc, z.2, htK]⟩
  choose Dv hDv hptsDv using fun j => hpts_aj (q j) εbar hεbar
  have hzres : schemeHomOverComp r hr zF = pts (x : JZero (N₀ * p)) := by
    apply Subtype.ext
    show r ≫ tb ≫ z.1 = _
    rw [reassoc_of% hrtb]
    exact hz
  have hares : ∀ j, schemeHomOverComp r hr (a j) = pts (Pic0.mk (Dv j)) := by
    intro j
    apply Subtype.ext
    show r ≫ (xF j).1 ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (DRLevel.R p) ℚ) = _
    rw [hptsDv j, hajbar, reassoc_of% (hxq j)]
  have hDv' : ∀ j, (Dv j : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      Finsupp.single (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1 := by
    intro j; rw [hDv j]; simp only [q, Equiv.apply_symm_apply]
  have hsum := E5W2bHgen.K6.pic0Mk_eq_sum_zsmul N₀ p hpN₀ 𝔓 εbar D₀ m idx pos neg hmult hn Dv hDv'
  have hzF := E5W2bHgen.K6.schemeHomOver_eq_prod_zpow_of_comp_eq_pts N₀ p hpN₀ 𝔓 D hD pts hpts_add tK r hr ⟨τF, rfl⟩ zF a
    (fun j => (pos j : ℤ) - (neg j : ℤ)) (x : JZero (N₀ * p)) (fun j => Pic0.mk (Dv j)) hzres hares (by rw [← hD₀]; exact hsum)

  have hx' : ∀ j, ((xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ)) ≫ DRLevel.toBase N₀ p = sF ≫ specMap (DRLevel.R p) ℚ := fun j => by
    rw [hxF1]; exact hxpt j
  obtain ⟨eF⟩ := E5W2bHgen.K6.nonempty_poincare_iso_foldr_of_eq_prod_zpow N₀ p hpN₀ 𝔓 D hD hDQ ajQ hPQ hajQ F sF zF m xF pos neg hn hw hzF hx'

  let ψ : SchemeHomOver tK (Spec.map (CommRingCat.ofHom ρO)) := ⟨tb, htK⟩
  have hbc : baseChangeSnd (DRLevel.toBase N₀ p) zF = baseChangeSnd (DRLevel.toBase N₀ p) ψ ≫ baseChangeSnd (DRLevel.toBase N₀ p) z :=
    (RelPicard.baseChangeSnd_comp (DRLevel.toBase N₀ p) z ψ).symm
  have ePz : (hD.poincare.pullbackAlong zF).L ≅
      (Scheme.Modules.pullback (baseChangeSnd (DRLevel.toBase N₀ p) ψ)).obj (hD.poincare.pullbackAlong z).L :=
    (Scheme.Modules.pullbackCongr hbc).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm

  have hxσ : ∀ j, ((tb ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO))) ≫
      DRLevel.toBase N₀ p = tK := hxpt
  have eFold := E5W2bHgen.K6a.foldr_ofPoint_congr (DRLevel.toBase N₀ p) tK
    (fun j => (xF j).1 ≫ pullback.fst (DRLevel.toBase N₀ p) (specMap (DRLevel.R p) ℚ))
    (fun j => (tb ≫ (σ j).1) ≫ 𝔛reg.toDR ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ρO)))
    hx' hxσ (funext hxF1) pos neg
  obtain ⟨eFo⟩ := eFold
  have hM := Nonempty.intro (ePz.symm ≪≫ eF ≪≫ eFo)

  obtain ⟨eY⟩ := E5W2bHgen.K5.genTransportInv N₀ p O ρO hpO 𝔛reg.Y 𝔛reg.toBase 𝔛reg.toDR 𝔛reg.toDR_over 𝔛reg.toDR_iso_generic
    (hD.poincare.pullbackAlong z).L m σ pos neg F (algebraMap O F) hτp tK htK hxσ hM
  exact ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫ eY⟩

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullback_toDR_poincare_pullbackAlong_iso_foldr_sectionTwist (solution)
