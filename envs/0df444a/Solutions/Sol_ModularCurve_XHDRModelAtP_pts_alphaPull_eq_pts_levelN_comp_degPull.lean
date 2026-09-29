-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.pts_alphaPull_eq_pts_levelN_comp_degPull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c3d151bb-5b63-5d26-80d9-a458fe610b64

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XH
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_pts_alphaPull_eq_pts_levelN_comp_degPull
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

noncomputable section

universe u v

local notation "ℚ̄" => AlgebraicClosure ℚ

local notation "tQ" => (specMap ℚ (AlgebraicClosure ℚ))

namespace PullPtsH

section K

abbrev cls {X : Scheme.{u}} (M : X.Modules) : Skeleton X.Modules := toSkeleton M

theorem cls_eq_iff {X : Scheme.{u}} (A B : X.Modules) : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun ⟨e⟩ => Quotient.sound ⟨e⟩⟩

theorem cls_congr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) : cls A = cls B :=
  (cls_eq_iff A B).2 ⟨e⟩

noncomputable def isoOfClsEq {X : Scheme.{u}} {A B : X.Modules} (h : cls A = cls B) : A ≅ B :=
  ((cls_eq_iff A B).1 h).some

theorem cls_tensor {X : Scheme.{u}} (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit (X : Scheme.{u}) : cls (𝟙_ X.Modules) = 1 := Skeleton.one_eq.symm

theorem isUnit_cls {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    IsUnit (cls L) := by
  obtain ⟨N, -, ⟨e⟩⟩ := hL.exists_tensor_inverse
  have h : cls L * cls N = 1 := ((cls_tensor L N).symm.trans (cls_congr e)).trans (cls_unit X)
  exact ⟨⟨cls L, cls N, h, (mul_comm _ _).trans h⟩, rfl⟩

theorem cls_mul_cls_dual {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    cls L * cls (Scheme.Modules.dual L) = 1 :=
  ((cls_tensor _ _).symm.trans (cls_congr hL.dual.2.some)).trans (cls_unit X)

theorem cls_pullback_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (h : cls A = cls B) :
    cls ((Scheme.Modules.pullback f).obj A) = cls ((Scheme.Modules.pullback f).obj B) :=
  cls_congr ((Scheme.Modules.pullback f).mapIso (isoOfClsEq h))

theorem cls_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj (A ⊗ B)) =
      cls ((Scheme.Modules.pullback f).obj A) * cls ((Scheme.Modules.pullback f).obj B) :=
  (cls_congr (Scheme.Modules.pullbackTensorObjIso f A B)).trans (cls_tensor _ _)

theorem cls_pullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cls ((Scheme.Modules.pullback f).obj (𝟙_ Y.Modules)) = 1 :=
  (cls_congr (Scheme.Modules.pullbackTensorUnitObjIso f)).trans (cls_unit X)

theorem cls_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    cls ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
      cls ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
  cls_congr ((Scheme.Modules.pullbackComp f g).app M)

theorem cls_pullback_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj M) = cls ((Scheme.Modules.pullback g).obj M) := by
  subst h; rfl

theorem cls_pullback_id {X : Scheme.{u}} (M : X.Modules) :
    cls ((Scheme.Modules.pullback (𝟙 X)).obj M) = cls M :=
  cls_congr ((Scheme.Modules.pullbackId X).app M)

theorem cls_pullback_inv_hom {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : Y.Modules) :
    cls ((Scheme.Modules.pullback (inv e)).obj ((Scheme.Modules.pullback e).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.inv_hom_id e), cls_pullback_id]

theorem cls_pullback_iso_inv_hom {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) :
    cls ((Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom e.inv_hom_id, cls_pullback_id]

theorem cls_eq_of_cls_pullback_eq {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {A B : Y.Modules}
    (h : cls ((Scheme.Modules.pullback e).obj A) = cls ((Scheme.Modules.pullback e).obj B)) :
    cls A = cls B := by
  rw [← cls_pullback_inv_hom e A, ← cls_pullback_inv_hom e B]
  exact cls_pullback_congr (inv e) h

theorem cls_invModule_mul {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    cls (I * J).invModule = cls I.invModule * cls J.invModule :=
  (cls_congr (hI.nonempty_mul_invModule_iso_tensor hJ).some).trans (cls_tensor _ _)

theorem cls_invModule_pow_mul {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (n : ℕ) :
    cls (I ^ n * J).invModule = cls I.invModule ^ n * cls J.invModule := by
  induction n generalizing J with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, mul_assoc, ih (hI.mul hJ), cls_invModule_mul hI hJ, pow_succ, mul_assoc]

theorem isInvertible_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i ^ n i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Scheme.IdealSheafData.isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).pow _).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cls_invModule_prod_pow_mul {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    cls ((∏ i ∈ s, I i ^ n i) * J).invModule = (∏ i ∈ s, cls (I i).invModule ^ n i) * cls J.invModule := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_mul, one_mul]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_assoc,
      cls_invModule_pow_mul (h a (Finset.mem_insert_self a s))
        ((isInvertible_prod_pow s I n fun i hi => h i (Finset.mem_insert_of_mem hi)).mul hJ),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hJ, mul_assoc]

theorem cls_invModule_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) :
    cls (∏ i ∈ s, I i ^ n i).invModule = ∏ i ∈ s, cls (I i).invModule ^ n i := by
  have hT := Scheme.IdealSheafData.isInvertible_top (X := X)
  have hP := isInvertible_prod_pow s I n h
  have h1 := cls_invModule_prod_pow_mul s I n h hT
  rw [cls_invModule_mul hP hT] at h1
  exact (isUnit_cls hT.isInvertible_invModule).mul_left_injective h1

theorem cls_rigidify_of_field {k : Type u} [Field k] {P : Scheme.{u}} (σ : Spec (CommRingCat.of k) ⟶ P)
    (q : P ⟶ Spec (CommRingCat.of k)) {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    cls (Scheme.Modules.rigidify σ q L) = cls L := by
  rw [Scheme.Modules.rigidify_def, cls_tensor]
  have h1 := (hL.pullback σ).dual.1
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ h1
  rw [cls_pullback_congr q (cls_congr e), cls_pullback_unit, mul_one]

end K

section P

theorem specMap_comp_specMap (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    specMap S T ≫ specMap R S = specMap R T := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R S T]

def liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

@[scoped simp] theorem liftPt_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    (liftPt D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

theorem eq_liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (z : SchemeHomOver t (D.baseChange R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = liftPt D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (liftPt_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

theorem poincare_liftPt_iso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (liftPt D R' t a)).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj (h.poincare.pullbackAlong a).L) := by
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  have E : baseChangeSnd (baseChange R c R') (liftPt D R' t a) ≫
      (BaseChange.κ c R' (D.baseChange R').toBase).hom ≫ baseChangeSnd c ψ₀ =
      (BaseChange.κ c R' t).hom ≫ baseChangeSnd c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst',
        BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc ((BaseChange.κ c R' _).hom),
        BaseChange.κ_hom_snd, ← Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, liftPt_fst,
        Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  refine ⟨(Scheme.Modules.pullback _).mapIso hP.some ≪≫ ?_⟩
  change (Scheme.Modules.pullback (baseChangeSnd _ (liftPt D R' t a))).obj
      ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).hom).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj h.poincare.L)) ≅
    (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c a)).obj h.poincare.L)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

theorem poincare_mul_iso {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h)
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk s) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

end P

section S

theorem isPullback_fst_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback c t)
  · rw [curveChange_snd, hf]
    exact IsPullback.of_hasPullback c' t
  · simp only [curveChange, pullback.lift_fst]

theorem curveChange_fst {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

theorem isFinite_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) [IsFinite f] :
    IsFinite (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange f hf t) inferInstance

theorem flat_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) [Flat f] :
    Flat (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_fst_curveChange f hf t) inferInstance

theorem locallyOfFinitePresentation_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_fst_curveChange f hf t) inferInstance

end S

section N

theorem isInvertible_ker_point {k : Type u} [Field k] {L : Type v} [Field L] [Algebra k L] (M : CurveModel k L)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) : x.1.ker.IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) x.1 x.2

theorem cls_pullback_invModule_ker
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    cls ((Scheme.Modules.pullback π).obj (x.1.ker).invModule) =
      ∏ w ∈ (M.pointEquivPlace x).fiber F',
        cls (((M'.pointEquivPlace.symm w).1.ker).invModule) ^ (w.ramificationIndex F) := by
  have hx : x.1.ker.IsInvertible := isInvertible_ker_point M x
  have hprod := CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex M M' π hπ hplace x
  have hinv : ((x.1.ker).comap π).IsInvertible := by
    rw [hprod]; exact isInvertible_prod_pow _ _ _ (fun w _ => isInvertible_ker_point M' _)
  rw [cls_congr (hx.nonempty_pullback_invModule_iso π hinv).some, hprod,
    cls_invModule_prod_pow _ _ _ (fun w _ => isInvertible_ker_point M' _)]

end N

section D

def genClass {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (v₀ u : Place K F) : Pic0 K F :=
  Pic0.mk ⟨Finsupp.single u 1 - Finsupp.single v₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp⟩

theorem genClass_eq_mk {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (v₀ u : Place K F) (Dv : Divisor.degZero (K := K) (F := F))
    (hDv : (Dv : Divisor K F) = Finsupp.single u 1 - Finsupp.single v₀ 1) :
    Pic0.mk Dv = genClass hdeg v₀ u := by
  unfold genClass; congr 1; exact Subtype.ext hDv

theorem closure_range_genClass_eq_top {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (v₀ : Place K F) :
    AddSubgroup.closure (Set.range (genClass hdeg v₀)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective x
  set S := AddSubgroup.closure (Set.range (genClass hdeg v₀)) with hS
  have hmemΨ : ∀ D : Divisor K F,
      D - Divisor.degree D • Finsupp.single v₀ (1 : ℤ) ∈ Divisor.degZero (K := K) (F := F) := by
    intro D
    rw [Divisor.mem_degZero, map_sub, map_zsmul, Divisor.degree_single, hdeg]
    simp
  let Ψ : Divisor K F →+ Divisor.degZero (K := K) (F := F) :=
    { toFun := fun D => ⟨_, hmemΨ D⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun D E => by
        apply Subtype.ext
        simp only [map_add, AddSubgroup.coe_add]
        rw [add_smul]
        abel }
  have hΨ : ∀ D : Divisor K F, (Ψ D : Divisor K F) = D - Divisor.degree D • Finsupp.single v₀ (1 : ℤ) :=
    fun _ => rfl
  let G : Divisor.degZero (K := K) (F := F) →+ Pic0 K F := QuotientAddGroup.mk' _
  have hG : ∀ D, Pic0.mk D = G D := fun _ => rfl
  have hall : ∀ D : Divisor K F, G (Ψ D) ∈ S := by
    intro D
    induction D using Finsupp.induction with
    | zero => rw [map_zero, map_zero]; exact S.zero_mem
    | single_add a b f _ _ ih =>
      rw [map_add, map_add]
      refine S.add_mem ?_ ih
      let φ : ℤ →+ Pic0 K F := (G.comp Ψ).comp (Finsupp.singleAddHom a)
      have hφ : ∀ n : ℤ, φ n = G (Ψ (Finsupp.single a n)) := fun _ => rfl
      have h1 : G (Ψ (Finsupp.single a 1)) = genClass hdeg v₀ a := by
        rw [← hG]
        unfold genClass
        congr 1
        apply Subtype.ext
        rw [hΨ, Divisor.degree_single, hdeg]
        simp
      rw [← hφ, AddMonoidHom.apply_int _ φ b, hφ, h1]
      exact S.zsmul_mem (AddSubgroup.subset_closure ⟨a, rfl⟩) b
  have hDv : Ψ (Dv : Divisor K F) = Dv := by
    apply Subtype.ext
    rw [hΨ, Divisor.mem_degZero.1 Dv.2, zero_smul, sub_zero]
  have := hall Dv
  rwa [hDv] at this

theorem sum_ramificationIndexAlong_eq_finrankAlong {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K F', w.deg = 1) (v : Place K F) :
    ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) = (finrankAlong K φ : ℤ) := by
  have h1 := Divisor.degree_pullbackAlong φ hφ hFI (Finsupp.single v 1)
  rw [Divisor.pullbackAlong_single, map_sum, Divisor.degree_single, hdeg] at h1
  simp only [Divisor.degree_single, hdeg', Nat.cast_one, mul_one, one_mul] at h1
  exact h1

theorem pull_genClass_add_sum_eq_sum {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K F', w.deg = 1)
    (pull : Pic0 K F →+ Pic0 K F')
    (hpull : ∀ (Dw : Divisor.degZero (K := K) (F := F)) (Dv : Divisor.degZero (K := K) (F := F')),
      (Dv : Divisor K F') = Divisor.pullbackAlong φ hφ (Dw : Divisor K F) → pull (Pic0.mk Dw) = Pic0.mk Dv)
    (v₀ v : Place K F) (s : Place K F') :
    pull (genClass hdeg v₀ v) +
        ∑ w ∈ Place.fiberAlong φ hφ v₀, w.ramificationIndexAlong φ • genClass hdeg' s w =
      ∑ w ∈ Place.fiberAlong φ hφ v, w.ramificationIndexAlong φ • genClass hdeg' s w := by
  classical

  have hmem' : ∀ u : Place K F', Finsupp.single u (1 : ℤ) - Finsupp.single s 1 ∈ Divisor.degZero (K := K) (F := F') := by
    intro u; rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg', hdeg']; simp
  set dgen : Place K F' → Divisor.degZero (K := K) (F := F') := fun u => ⟨_, hmem' u⟩ with hdgen
  have hgc : ∀ u, genClass hdeg' s u = Pic0.mk (dgen u) := fun u => rfl

  have hmem : Finsupp.single v (1 : ℤ) - Finsupp.single v₀ 1 ∈ Divisor.degZero (K := K) (F := F) := by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp
  let Dw : Divisor.degZero (K := K) (F := F) := ⟨_, hmem⟩
  let Dv : Divisor.degZero (K := K) (F := F') :=
    ⟨Divisor.pullbackAlong φ hφ (Dw : Divisor K F), Divisor.pullbackAlong_mem_degZero φ hφ hFI Dw.2⟩
  have hgen : genClass hdeg v₀ v = Pic0.mk Dw := rfl
  rw [hgen, hpull Dw Dv rfl]

  let G : Divisor.degZero (K := K) (F := F') →+ Pic0 K F' := QuotientAddGroup.mk' _
  have hG : ∀ D, Pic0.mk D = G D := fun _ => rfl
  have hsum : ∀ u : Place K F, ∑ w ∈ Place.fiberAlong φ hφ u, (w.ramificationIndexAlong φ : ℤ) = finrankAlong K φ :=
    fun u => sum_ramificationIndexAlong_eq_finrankAlong φ hφ hFI hdeg hdeg' u
  simp only [hgc]
  simp only [hG, ← map_nsmul, ← map_sum, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, AddSubgroup.val_finsetSum, AddSubgroup.coe_nsmul, hdgen, Dv, Dw,
    map_sub, Divisor.pullbackAlong_single, one_mul, smul_sub, Finset.sum_sub_distrib,
    Finsupp.smul_single, nsmul_eq_mul, mul_one]
  have h1 : ∀ u : Place K F, ∑ x ∈ Place.fiberAlong φ hφ u,
      Finsupp.single s ((x.ramificationIndexAlong φ : ℕ) : ℤ) = Finsupp.single s ((finrankAlong K φ : ℕ) : ℤ) := by
    intro u; rw [← Finsupp.single_finsetSum, hsum u]
  rw [h1, h1]
  abel

end D

section A

scoped instance finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem exists_transcendental_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ x : xHFunctionFieldBar M H, Transcendental ℚ̄ x ∧
      FiniteDimensional (IntermediateField.adjoin ℚ̄ ({x} : Set (xHFunctionFieldBar M H))) (xHFunctionFieldBar M H) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚ̄ (CohCarrier.GammaH M H)
    (ModularCurve.translation_mem_GammaH M H)

theorem isCurveOver_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver ℚ̄ (xHFunctionFieldBar M H) := by
  obtain ⟨x, htr, hfd⟩ := exists_transcendental_xHFunctionFieldBar M H
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd

theorem deg_eq_one_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∀ v : Place ℚ̄ (xHFunctionFieldBar M H), v.deg = 1 :=
  haveI := isCurveOver_xHFunctionFieldBar M H
  IsCurveOver.forall_deg_eq_one_of_isAlgClosed

theorem essFiniteType_of_finiteDimensional_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  haveI : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  haveI : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F := hfd
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

theorem essFiniteType_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Algebra.EssFiniteType ℚ̄ (xHFunctionFieldBar M H) := by
  obtain ⟨x, -, hfd⟩ := exists_transcendental_xHFunctionFieldBar M H
  exact essFiniteType_of_finiteDimensional_adjoin x hfd

theorem finiteAlong_of_isIntegral_of_exists_finiteDimensional_adjoin {K F₀ F : Type*} [Field K] [Field F₀] [Field F]
    [Algebra K F₀] [Algebra K F] (φ : F₀ →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral)
    (h : ∃ x : F, FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    FiniteAlong K φ := by
  classical
  obtain ⟨x, hfd⟩ := h
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Algebra.IsIntegral F₀ F := isIntegral_along φ hφ
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  haveI : FiniteDimensional E F := hfd
  let b := Module.finBasis E F
  let S : Set F := insert x (Set.range b)
  haveI : Finite S := ((Set.finite_range b).insert x).to_subtype
  have hint : ∀ y ∈ S, IsIntegral F₀ y := fun y _ => Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional F₀ (IntermediateField.adjoin F₀ S) := IntermediateField.finiteDimensional_adjoin hint
  have hxS : x ∈ IntermediateField.adjoin F₀ S := IntermediateField.subset_adjoin F₀ S (Set.mem_insert x _)
  have hE_le : ∀ e : E, (e : F) ∈ IntermediateField.adjoin F₀ S := by
    have hle : E ≤ (IntermediateField.adjoin F₀ S).restrictScalars K := by
      rw [hE, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact hxS
    exact fun e => hle e.2
  have htop : IntermediateField.adjoin F₀ S = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [← b.sum_repr y]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (hE_le _) (IntermediateField.subset_adjoin F₀ S (Set.mem_insert_of_mem x ⟨i, rfl⟩))
  have hfin : FiniteDimensional F₀ (⊤ : IntermediateField F₀ F) := by rw [← htop]; infer_instance
  exact (IntermediateField.topEquiv (F := F₀) (E := F)).toLinearEquiv.finiteDimensional

theorem separableAlong_of_charZero {K F₀ F : Type*} [Field K] [Field F₀] [Field F] [CharZero F₀]
    [Algebra K F₀] [Algebra K F] (φ : F₀ →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  letI := algebraAlong φ
  haveI : Algebra.IsIntegral F₀ F := isIntegral_along φ hφ
  haveI : Algebra.IsAlgebraic F₀ F := Algebra.IsIntegral.isAlgebraic
  haveI : PerfectField F₀ := PerfectField.ofCharZero
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem fundamentalIdentityAlong_xHFunctionFieldBar (M₀ : ℕ) [NeZero M₀] (H₀ : Subgroup (ZMod M₀)ˣ)
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) [HasPrincipalDivisors ℚ̄ (xHFunctionFieldBar M H)]
    (φ : xHFunctionFieldBar M₀ H₀ →ₐ[ℚ̄] xHFunctionFieldBar M H) (hφ : φ.toRingHom.IsIntegral) :
    FundamentalIdentityAlong ℚ̄ φ hφ := by
  have hfin : FiniteAlong ℚ̄ φ := by
    obtain ⟨x, -, hfd⟩ := exists_transcendental_xHFunctionFieldBar M H
    exact finiteAlong_of_isIntegral_of_exists_finiteDimensional_adjoin φ hφ ⟨x, hfd⟩
  haveI : CharZero (xHFunctionFieldBar M₀ H₀) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (xHFunctionFieldBar M₀ H₀)).injective
  exact AlgebraicCurve.fundamentalIdentityAlong φ hφ hfin (separableAlong_of_charZero φ hφ)

end A

section G

theorem toMul_map_sum_nsmul {A M ι : Type*} [AddCommMonoid A] [CommMonoid M] (χ : A →+ Additive M)
    (s : Finset ι) (n : ι → ℕ) (a : ι → A) :
    Additive.toMul (χ (∑ i ∈ s, n i • a i)) = ∏ i ∈ s, Additive.toMul (χ (a i)) ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero]; rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add, toMul_add, ih, map_nsmul, toMul_nsmul]

theorem κ_inv_snd {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ c R' t).inv ≫ pullback.snd (baseChange R c R') t = pullback.snd c (t ≫ specMap R R') := by
  rw [Iso.inv_comp_eq, BaseChange.κ_hom_snd]

theorem κ_inv_fst_fst {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ c R' t).inv ≫ pullback.fst (baseChange R c R') t ≫ pullback.fst c (specMap R R') =
      pullback.fst c (t ≫ specMap R R') := by
  rw [Iso.inv_comp_eq, BaseChange.κ_hom_fst]

theorem κ_inv_fst_snd {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ c R' t).inv ≫ pullback.fst (baseChange R c R') t ≫ pullback.snd c (specMap R R') =
      pullback.snd c (t ≫ specMap R R') ≫ t := by
  rw [← κ_inv_snd c R' t, Category.assoc, ← pullback.condition]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem cls_poincare_pts_genClass
    {R : Type} [CommRing R] [Algebra R ℚ] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated (baseChange R c ℚ)] [SmoothOfRelativeDimension 1 (baseChange R c ℚ)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hDQ : RepresentsRelSubPic (baseChange R c ℚ) (sectionBaseChange ℚ ε)
        (algEquivZeroCut (baseChange R c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR c ε ℚ
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange R c ℚ) (D.baseChange ℚ).toBase)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange R c ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange R c ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R c ℚ) (t ≫ (sectionBaseChange ℚ ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ ε).2).trans
              (Category.comp_id t)))).idealModule))
    {F : Type} [Field F] [Algebra ℚ̄ F]
    (Mη : CurveModel ℚ̄ F) (eη : Mη.C ⟶ pullback c (specMap ℚ ℚ̄ ≫ specMap R ℚ)) [IsIso eη]
    (heη : eη ≫ pullback.snd _ _ = Mη.toBase)
    (pts : Pic0 ℚ̄ F → SchemeHomOver (specMap ℚ ℚ̄ ≫ specMap R ℚ) D.toBase)
    (s Q : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hs : s.1 ≫ eη ≫ pullback.fst c _ = (specMap ℚ ℚ̄ ≫ specMap R ℚ) ≫ ε.1)
    (Dv : Divisor.degZero (K := ℚ̄) (F := F))
    (hpts : (pts (Pic0.mk Dv)).1 = Q.1 ≫ eη ≫ (BaseChange.κ c ℚ (specMap ℚ ℚ̄)).inv ≫
      pullback.fst (baseChange R c ℚ) (specMap ℚ ℚ̄) ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap R ℚ)) :
    cls ((Scheme.Modules.pullback eη).obj (h.poincare.pullbackAlong (pts (Pic0.mk Dv))).L) =
      cls (Q.1.ker).invModule * cls (s.1.ker).module := by

  have hxQ : (Q.1 ≫ eη ≫ (BaseChange.κ c ℚ tQ).inv ≫ pullback.fst (baseChange R c ℚ) tQ) ≫ baseChange R c ℚ = tQ := by
    change (Q.1 ≫ eη ≫ (BaseChange.κ c ℚ tQ).inv ≫ pullback.fst (baseChange R c ℚ) tQ) ≫ pullback.snd c (specMap R ℚ) = tQ
    simp only [Category.assoc]
    rw [κ_inv_fst_snd, reassoc_of% heη, reassoc_of% Q.2]
  let xQ : SchemeHomOver tQ (baseChange R c ℚ) := ⟨_, hxQ⟩
  let z : SchemeHomOver tQ (D.baseChange ℚ).toBase :=
    ⟨xQ.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (xQ.1 ≫ ·) ajQ.2).trans xQ.2)⟩
  have hz : z = liftPt D ℚ tQ (pts (Pic0.mk Dv)) := by
    apply eq_liftPt
    rw [hpts]
    simp only [z, xQ, Category.assoc]
  obtain ⟨e1⟩ := poincare_liftPt_iso c ε D h ℚ hDQ hPQ tQ (pts (Pic0.mk Dv))
  rw [← hz] at e1
  obtain ⟨e2⟩ := hajQ ℚ̄ tQ xQ

  have hEsnd : (eη ≫ (BaseChange.κ c ℚ tQ).inv) ≫ pullback.snd (baseChange R c ℚ) tQ = Mη.toBase := by
    rw [Category.assoc, κ_inv_snd, heη]
  have hpQ : Q.1 ≫ eη ≫ (BaseChange.κ c ℚ tQ).inv = graphOver (baseChange R c ℚ) xQ.1 xQ.2 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, graphOver_fst, xQ]
    · rw [graphOver_snd, Category.assoc, hEsnd, Q.2]
  have hps : s.1 ≫ eη ≫ (BaseChange.κ c ℚ tQ).inv = graphOver (baseChange R c ℚ) (tQ ≫ (sectionBaseChange ℚ ε).1)
      ((Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) (sectionBaseChange ℚ ε).2).trans (Category.comp_id tQ))) := by
    apply pullback.hom_ext
    · rw [graphOver_fst]
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [κ_inv_fst_fst, sectionBaseChange_coe_fst, hs, Category.assoc]
      · simp only [Category.assoc]
        rw [κ_inv_fst_snd, sectionBaseChange_coe_snd, reassoc_of% heη, reassoc_of% s.2, Category.comp_id]
    · rw [graphOver_snd, Category.assoc, hEsnd, s.2]
  obtain ⟨iQ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (eη ≫ (BaseChange.κ c ℚ tQ).inv)
    (graphOver (baseChange R c ℚ) xQ.1 xQ.2) Q.1 hpQ
    (RelEffCartierDiv.ofPoint (baseChange R c ℚ) xQ.1 xQ.2).isInvertible_I (isInvertible_ker_point Mη Q) 1).1
  obtain ⟨is⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (eη ≫ (BaseChange.κ c ℚ tQ).inv) _ s.1 hps
    (RelEffCartierDiv.ofPoint (baseChange R c ℚ) _ _).isInvertible_I (isInvertible_ker_point Mη s) 1).2
  simp only [pow_one] at iQ is

  have e3 : cls ((Scheme.Modules.pullback (BaseChange.κ c ℚ tQ).hom).obj (h.poincare.pullbackAlong (pts (Pic0.mk Dv))).L) =
      cls ((RelEffCartierDiv.ofPoint (baseChange R c ℚ) xQ.1 xQ.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R c ℚ) (tQ ≫ (sectionBaseChange ℚ ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) (sectionBaseChange ℚ ε).2).trans
              (Category.comp_id tQ)))).idealModule) :=
    (cls_congr e1).symm.trans (cls_congr e2)
  have e4 : cls ((Scheme.Modules.pullback eη).obj (h.poincare.pullbackAlong (pts (Pic0.mk Dv))).L) =
      cls ((Scheme.Modules.pullback (eη ≫ (BaseChange.κ c ℚ tQ).inv)).obj
        ((Scheme.Modules.pullback (BaseChange.κ c ℚ tQ).hom).obj (h.poincare.pullbackAlong (pts (Pic0.mk Dv))).L)) := by
    exact (cls_pullback_congr eη (cls_pullback_iso_inv_hom (BaseChange.κ c ℚ tQ) _).symm).trans (cls_pullback_comp _ _ _)
  rw [e4, cls_pullback_congr _ e3, cls_pullback_tensor]
  exact congrArg₂ (· * ·) (cls_congr iQ) (cls_congr is)

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pts_pull_eq_pts_comp
    {R : Type} [CommRing R] [Algebra R ℚ]
    {CM CN : Scheme.{0}} (cM : CM ⟶ Spec (CommRingCat.of R)) (cN : CN ⟶ Spec (CommRingCat.of R))
    [IsSeparated (baseChange R cM ℚ)] [SmoothOfRelativeDimension 1 (baseChange R cM ℚ)]
    [IsSeparated (baseChange R cN ℚ)] [SmoothOfRelativeDimension 1 (baseChange R cN ℚ)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cM) (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cN)
    (g : Spec (CommRingCat.of ℚ̄) ⟶ Spec (CommRingCat.of R)) (hg : g = tQ ≫ specMap R ℚ)

    (D : RelativePic0Designation R cM) (h : RepresentsRelSubPic cM ε (algEquivZeroCut cM ε) D)
    (hDQ : RepresentsRelSubPic (baseChange R cM ℚ) (sectionBaseChange ℚ ε)
        (algEquivZeroCut (baseChange R cM ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR cM ε ℚ
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange R cM ℚ) (D.baseChange ℚ).toBase)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange R cM ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange R cM ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R cM ℚ) (t ≫ (sectionBaseChange ℚ ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ ε).2).trans
              (Category.comp_id t)))).idealModule))
    (kQ : pullback cM g ⟶ pullback cM (specMap R ℚ))
    (hkQ₁ : kQ ≫ pullback.fst cM (specMap R ℚ) = pullback.fst cM g)
    (hkQ₂ : kQ ≫ pullback.snd cM (specMap R ℚ) = pullback.snd cM g ≫ tQ)
    {F : Type} [Field F] [Algebra ℚ̄ F] [IsCurveOver ℚ̄ F] [Algebra.EssFiniteType ℚ̄ F]
    (Mη : CurveModel ℚ̄ F) (eη : Mη.C ⟶ pullback cM g) [IsIso eη] (heη : eη ≫ pullback.snd _ _ = Mη.toBase)
    (ajbar : Mη.C ⟶ D.P) (hajbar : ajbar = eη ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap R ℚ))
    (εbar : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst cM g = g ≫ ε.1)
    (pts : Pic0 ℚ̄ F → SchemeHomOver g D.toBase)
    (hpts_add : ∀ x y : Pic0 ℚ̄ F,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h).mul _ (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst cM g = g ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := ℚ̄) (F := F),
        (Dv : Divisor ℚ̄ F) = Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (D₀ : RelativePic0Designation R cN) (h₀ : RepresentsRelSubPic cN ε₀ (algEquivZeroCut cN ε₀) D₀)
    (hDQ₀ : RepresentsRelSubPic (baseChange R cN ℚ) (sectionBaseChange ℚ ε₀)
        (algEquivZeroCut (baseChange R cN ℚ) (sectionBaseChange ℚ ε₀)) (D₀.baseChange ℚ))
    (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR cN ε₀ ℚ
        (h₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R ℚ), pullback.condition⟩)).L))
    (ajQ₀ : SchemeHomOver (baseChange R cN ℚ) (D₀.baseChange ℚ).toBase)
    (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange R cN ℚ)),
      Nonempty ((hDQ₀.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange R cN ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R cN ℚ) (t ≫ (sectionBaseChange ℚ ε₀).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ ε₀).2).trans
              (Category.comp_id t)))).idealModule))
    (kQ₀ : pullback cN g ⟶ pullback cN (specMap R ℚ))
    (hkQ₀₁ : kQ₀ ≫ pullback.fst cN (specMap R ℚ) = pullback.fst cN g)
    (hkQ₀₂ : kQ₀ ≫ pullback.snd cN (specMap R ℚ) = pullback.snd cN g ≫ tQ)
    {F₀ : Type} [Field F₀] [Algebra ℚ̄ F₀] [IsCurveOver ℚ̄ F₀] [Algebra.EssFiniteType ℚ̄ F₀]
    (Mη₀ : CurveModel ℚ̄ F₀) (eη₀ : Mη₀.C ⟶ pullback cN g) [IsIso eη₀] (heη₀ : eη₀ ≫ pullback.snd _ _ = Mη₀.toBase)
    (ajbar₀ : Mη₀.C ⟶ D₀.P) (hajbar₀ : ajbar₀ = eη₀ ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst D₀.toBase (specMap R ℚ))
    (εbar₀ : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη₀.C // q ≫ Mη₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eη₀ ≫ pullback.fst cN g = g ≫ ε₀.1)
    (pts₀ : Pic0 ℚ̄ F₀ → SchemeHomOver g D₀.toBase)
    (hpts₀_add : ∀ x y : Pic0 ℚ̄ F₀,
      pts₀ (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h₀).mul _ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη₀.C // q ≫ Mη₀.toBase = 𝟙 _}),
      s.1 ≫ eη₀ ≫ pullback.fst cN g = g ≫ ε₀.1 →
      ∃ Dv : Divisor.degZero (K := ℚ̄) (F := F₀),
        (Dv : Divisor ℚ̄ F₀) = Finsupp.single (Mη₀.pointEquivPlace x) 1 - Finsupp.single (Mη₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)

    (πR : SchemeHomOver cM cN) [IsFinite πR.1] [Flat πR.1] [LocallyOfFinitePresentation πR.1]
    [HasPrincipalDivisors ℚ̄ F]
    (φ : F₀ →ₐ[ℚ̄] F) (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong ℚ̄ φ hφ)
    (hplace : ∀ (y : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y₀ : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη₀.C // q ≫ Mη₀.toBase = 𝟙 _}),
      y₀.1 ≫ eη₀ ≫ pullback.fst _ _ = y.1 ≫ eη ≫ pullback.fst _ _ ≫ πR.1 →
      Mη₀.pointEquivPlace y₀ = Place.restrictAlong φ hφ (Mη.pointEquivPlace y))
    (pull : Pic0 ℚ̄ F₀ →+ Pic0 ℚ̄ F)
    (hpull : ∀ (Dw : Divisor.degZero (K := ℚ̄) (F := F₀)) (Dv : Divisor.degZero (K := ℚ̄) (F := F)),
      (Dv : Divisor ℚ̄ F) = Divisor.pullbackAlong φ hφ (Dw : Divisor ℚ̄ F₀) → pull (Pic0.mk Dw) = Pic0.mk Dv)
    (deg : SchemeHomOver D₀.toBase D.toBase)
    (hdegp : ∀ b : SchemeHomOver g D₀.toBase,
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b deg)).L ≅
        Scheme.Modules.rigidify (rigSection cM g ε) (pullback.snd cM g)
          ((Scheme.Modules.pullback (curveChange πR.1 πR.2 g)).obj (h₀.poincare.pullbackAlong b).L)))
    (x : Pic0 ℚ̄ F₀) :
    (pts (pull x)).1 = (pts₀ x).1 ≫ deg.1 := by
  subst hg
  classical
  have hdeg : ∀ v : Place ℚ̄ F, v.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hdeg₀ : ∀ v : Place ℚ̄ F₀, v.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ

  have hkQ : kQ = (BaseChange.κ cM ℚ tQ).inv ≫ pullback.fst (baseChange R cM ℚ) tQ := by
    apply pullback.hom_ext
    · rw [hkQ₁, Category.assoc, κ_inv_fst_fst]
    · rw [hkQ₂, Category.assoc, κ_inv_fst_snd]
  have hkQ₀ : kQ₀ = (BaseChange.κ cN ℚ tQ).inv ≫ pullback.fst (baseChange R cN ℚ) tQ := by
    apply pullback.hom_ext
    · rw [hkQ₀₁, Category.assoc, κ_inv_fst_fst]
    · rw [hkQ₀₂, Category.assoc, κ_inv_fst_snd]

  haveI := isFinite_curveChange πR.1 πR.2 (tQ ≫ specMap R ℚ)
  haveI := flat_curveChange πR.1 πR.2 (tQ ≫ specMap R ℚ)
  haveI := locallyOfFinitePresentation_curveChange πR.1 πR.2 (tQ ≫ specMap R ℚ)
  obtain ⟨πbar, hπbar_def⟩ : ∃ πbar : Mη.C ⟶ Mη₀.C, πbar = eη ≫ curveChange πR.1 πR.2 (tQ ≫ specMap R ℚ) ≫ inv eη₀ :=
    ⟨_, rfl⟩
  haveI : IsFinite πbar := by rw [hπbar_def]; infer_instance
  haveI : Flat πbar := by rw [hπbar_def]; infer_instance
  haveI : LocallyOfFinitePresentation πbar := by rw [hπbar_def]; infer_instance
  have hπbar : πbar ≫ Mη₀.toBase = Mη.toBase := by
    have h1 : inv eη₀ ≫ Mη₀.toBase = pullback.snd cN _ := by rw [← heη₀, IsIso.inv_hom_id_assoc]
    rw [hπbar_def, Category.assoc, Category.assoc, h1, curveChange_snd, heη]
  have hπeη : πbar ≫ eη₀ = eη ≫ curveChange πR.1 πR.2 _ := by
    rw [hπbar_def]; simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hplace' : ∀ (y : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (y₀ : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη₀.C // q ≫ Mη₀.toBase = 𝟙 _}),
      y.1 ≫ πbar = y₀.1 → (Mη.pointEquivPlace y).restrict F₀ = Mη₀.pointEquivPlace y₀ := by
    intro y y₀ hy
    have key := hplace y y₀ (by
      rw [← hy, Category.assoc, ← Category.assoc πbar, hπeη, Category.assoc, curveChange_fst])
    exact key.symm

  have hIs : Scheme.Modules.IsInvertible (εbar.1.ker).module := (isInvertible_ker_point Mη εbar).isInvertible_module
  have hIs₀ : Scheme.Modules.IsInvertible (εbar₀.1.ker).module := (isInvertible_ker_point Mη₀ εbar₀).isInvertible_module

  set χf : Pic0 ℚ̄ F → Skeleton (Mη.C).Modules := fun y =>
    cls ((Scheme.Modules.pullback eη).obj (h.poincare.pullbackAlong (pts y)).L) with hχf
  have χmul : ∀ a b, χf (a + b) = χf a * χf b := fun a b => by
    simp only [hχf]
    rw [hpts_add a b, cls_pullback_congr _ (cls_congr (poincare_mul_iso h _ _ _).some), cls_pullback_tensor]
  have χunit : ∀ a, IsUnit (χf a) := fun a =>
    isUnit_cls (((h.poincare.pullbackAlong (pts a)).isInvertible).pullback eη)
  have χzero : χf 0 = 1 := by
    have h1 := χmul 0 0
    rw [add_zero] at h1
    exact (χunit 0).mul_left_cancel (h1.symm.trans (mul_one _).symm)

  set ρf : Pic0 ℚ̄ F₀ → Skeleton (Mη.C).Modules := fun z =>
    cls ((Scheme.Modules.pullback πbar).obj ((Scheme.Modules.pullback eη₀).obj (h₀.poincare.pullbackAlong (pts₀ z)).L))
    with hρf
  have ρmul : ∀ a b, ρf (a + b) = ρf a * ρf b := fun a b => by
    simp only [hρf]
    rw [hpts₀_add a b, cls_pullback_congr πbar ((cls_pullback_congr _ (cls_congr (poincare_mul_iso h₀ _ _ _).some)).trans
      ((cls_pullback_tensor eη₀ _ _).trans (cls_tensor _ _).symm)), cls_pullback_tensor]
  have ρunit : ∀ a, IsUnit (ρf a) := fun a =>
    isUnit_cls ((((h₀.poincare.pullbackAlong (pts₀ a)).isInvertible).pullback eη₀).pullback πbar)
  have ρzero : ρf 0 = 1 := by
    have h1 := ρmul 0 0
    rw [add_zero] at h1
    exact (ρunit 0).mul_left_cancel (h1.symm.trans (mul_one _).symm)

  have hρ : ∀ z, cls ((Scheme.Modules.pullback eη).obj
      (h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp (pts₀ z) deg)).L) = ρf z := by
    intro z
    obtain ⟨e⟩ := hdegp (pts₀ z)
    have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange πR.1 πR.2 _)).obj
        (h₀.poincare.pullbackAlong (pts₀ z)).L) := (h₀.poincare.pullbackAlong (pts₀ z)).isInvertible.pullback _
    simp only [hρf]
    rw [cls_pullback_congr eη (cls_congr e), cls_pullback_congr eη (cls_rigidify_of_field _ _ hN), cls_pullback_comp,
      cls_pullback_comp, cls_pullback_congr_hom hπeη]

  have hχg : ∀ w : Place ℚ̄ F, χf (genClass hdeg (Mη.pointEquivPlace εbar) w) =
      cls (((Mη.pointEquivPlace.symm w).1).ker).invModule * cls (εbar.1.ker).module := by
    intro w
    obtain ⟨Dv, hDv, hpts⟩ := hpts_aj (Mη.pointEquivPlace.symm w) εbar hεbar
    rw [Equiv.apply_symm_apply] at hDv
    rw [← genClass_eq_mk hdeg _ w Dv hDv]
    simp only [hχf]
    refine cls_poincare_pts_genClass cM ε D h hDQ hPQ ajQ hajQ Mη eη heη pts εbar (Mη.pointEquivPlace.symm w) hεbar Dv ?_
    rw [hpts, hajbar, hkQ]; simp only [Category.assoc]

  have hχg₀ : ∀ u : Place ℚ̄ F₀, cls ((Scheme.Modules.pullback eη₀).obj
      (h₀.poincare.pullbackAlong (pts₀ (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) u))).L) =
      cls (((Mη₀.pointEquivPlace.symm u).1).ker).invModule * cls (εbar₀.1.ker).module := by
    intro u
    obtain ⟨Dv, hDv, hpts⟩ := hpts₀_aj (Mη₀.pointEquivPlace.symm u) εbar₀ hεbar₀
    rw [Equiv.apply_symm_apply] at hDv
    rw [← genClass_eq_mk hdeg₀ _ u Dv hDv]
    refine cls_poincare_pts_genClass cN ε₀ D₀ h₀ hDQ₀ hPQ₀ ajQ₀ hajQ₀ Mη₀ eη₀ heη₀ pts₀ εbar₀ (Mη₀.pointEquivPlace.symm u)
      hεbar₀ Dv ?_
    rw [hpts, hajbar₀, hkQ₀]; simp only [Category.assoc]

  set OB : Place ℚ̄ F → Skeleton (Mη.C).Modules := fun w => cls (((Mη.pointEquivPlace.symm w).1).ker).invModule with hOB
  set PB : Place ℚ̄ F₀ → Skeleton (Mη.C).Modules := fun u =>
    ∏ w ∈ Place.fiberAlong φ hφ u, OB w ^ (w.ramificationIndexAlong φ) with hPB
  have hOBunit : ∀ w, IsUnit (OB w) := fun w => isUnit_cls (isInvertible_ker_point Mη _).isInvertible_invModule
  have hPBunit : ∀ u, IsUnit (PB u) := fun u =>
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun w _ => (hOBunit w).pow _)
  have hPull : ∀ Q : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη₀.C // q ≫ Mη₀.toBase = 𝟙 _},
      cls ((Scheme.Modules.pullback πbar).obj (Q.1.ker).invModule) = PB (Mη₀.pointEquivPlace Q) := by
    intro Q
    exact cls_pullback_invModule_ker Mη₀ Mη πbar hπbar hplace' Q

  have hB : cls ((Scheme.Modules.pullback πbar).obj (εbar₀.1.ker).module) * PB (Mη₀.pointEquivPlace εbar₀) = 1 := by
    have hmi : cls ((εbar₀.1.ker).module ⊗ (εbar₀.1.ker).invModule) = cls (𝟙_ _) := by
      rw [cls_tensor, cls_unit]; exact cls_mul_cls_dual hIs₀
    rw [← hPull εbar₀, ← cls_pullback_tensor, cls_pullback_congr πbar hmi, cls_pullback_unit]

  have hsum : ∀ u : Place ℚ̄ F₀, ∑ w ∈ Place.fiberAlong φ hφ u, w.ramificationIndexAlong φ = finrankAlong ℚ̄ φ := by
    intro u; exact_mod_cast sum_ramificationIndexAlong_eq_finrankAlong φ hφ hFI hdeg₀ hdeg u
  have hprod : ∀ u : Place ℚ̄ F₀, ∏ w ∈ Place.fiberAlong φ hφ u, (OB w * cls (εbar.1.ker).module) ^ (w.ramificationIndexAlong φ) =
      PB u * cls (εbar.1.ker).module ^ finrankAlong ℚ̄ φ := by
    intro u
    simp only [hPB, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum u]

  let χ : Pic0 ℚ̄ F →+ Additive (Skeleton (Mη.C).Modules) :=
    { toFun := fun y => Additive.ofMul (χf y)
      map_zero' := by simp only [χzero, ofMul_one]
      map_add' := fun a b => by simp only [χmul, ofMul_mul] }
  let ρ : Pic0 ℚ̄ F₀ →+ Additive (Skeleton (Mη.C).Modules) :=
    { toFun := fun z => Additive.ofMul (ρf z)
      map_zero' := by simp only [ρzero, ofMul_one]
      map_add' := fun a b => by simp only [ρmul, ofMul_mul] }
  have hχ : ∀ y, χ y = Additive.ofMul (χf y) := fun _ => rfl
  have hρ' : ∀ z, ρ z = Additive.ofMul (ρf z) := fun _ => rfl

  have hgen_case : ∀ u : Place ℚ̄ F₀,
      χf (pull (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) u)) = ρf (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) u) := by
    intro u
    obtain ⟨Q, rfl⟩ := Mη₀.pointEquivPlace.surjective u

    have hT := pull_genClass_add_sum_eq_sum φ hφ hFI hdeg₀ hdeg pull hpull (Mη₀.pointEquivPlace εbar₀)
      (Mη₀.pointEquivPlace Q) (Mη.pointEquivPlace εbar)
    have hχT : χf (pull (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) (Mη₀.pointEquivPlace Q))) *
        ∏ w ∈ Place.fiberAlong φ hφ (Mη₀.pointEquivPlace εbar₀), (OB w * cls (εbar.1.ker).module) ^ (w.ramificationIndexAlong φ) =
        ∏ w ∈ Place.fiberAlong φ hφ (Mη₀.pointEquivPlace Q), (OB w * cls (εbar.1.ker).module) ^ (w.ramificationIndexAlong φ) := by
      have h0 := congrArg (fun z => Additive.toMul (χ z)) hT
      try dsimp only at h0
      rw [map_add, toMul_add, toMul_map_sum_nsmul, toMul_map_sum_nsmul] at h0
      have h2 : ∀ v : Place ℚ̄ F₀,
          ∏ w ∈ Place.fiberAlong φ hφ v, Additive.toMul (χ (genClass hdeg (Mη.pointEquivPlace εbar) w)) ^ (w.ramificationIndexAlong φ) =
            ∏ w ∈ Place.fiberAlong φ hφ v, (OB w * cls (εbar.1.ker).module) ^ (w.ramificationIndexAlong φ) := by
        intro v
        exact Finset.prod_congr rfl (fun w _ => by rw [← hχg w]; rfl)
      rw [h2, h2] at h0
      exact h0
    rw [hprod, hprod] at hχT

    have hR : ρf (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) (Mη₀.pointEquivPlace Q)) =
        PB (Mη₀.pointEquivPlace Q) * cls ((Scheme.Modules.pullback πbar).obj (εbar₀.1.ker).module) := by
      have h2 := hχg₀ (Mη₀.pointEquivPlace Q)
      rw [Equiv.symm_apply_apply] at h2
      simp only [hρf]
      rw [cls_pullback_congr πbar (h2.trans (cls_tensor _ _).symm), cls_pullback_tensor, hPull Q]

    have hunit : IsUnit (PB (Mη₀.pointEquivPlace εbar₀) * cls (εbar.1.ker).module ^ finrankAlong ℚ̄ φ) :=
      (hPBunit _).mul ((isUnit_cls hIs).pow _)
    apply hunit.mul_left_injective
    change χf (pull (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) (Mη₀.pointEquivPlace Q))) *
        (PB (Mη₀.pointEquivPlace εbar₀) * cls (εbar.1.ker).module ^ finrankAlong ℚ̄ φ) =
      ρf (genClass hdeg₀ (Mη₀.pointEquivPlace εbar₀) (Mη₀.pointEquivPlace Q)) *
        (PB (Mη₀.pointEquivPlace εbar₀) * cls (εbar.1.ker).module ^ finrankAlong ℚ̄ φ)
    rw [hχT, hR]
    rw [show PB (Mη₀.pointEquivPlace Q) * cls ((Scheme.Modules.pullback πbar).obj (εbar₀.1.ker).module) *
        (PB (Mη₀.pointEquivPlace εbar₀) * cls (εbar.1.ker).module ^ finrankAlong ℚ̄ φ) =
        PB (Mη₀.pointEquivPlace Q) * (cls ((Scheme.Modules.pullback πbar).obj (εbar₀.1.ker).module) *
          PB (Mη₀.pointEquivPlace εbar₀)) * cls (εbar.1.ker).module ^ finrankAlong ℚ̄ φ by simp only [mul_assoc],
      hB, mul_one]

  have hgen := closure_range_genClass_eq_top hdeg₀ (Mη₀.pointEquivPlace εbar₀)
  have heq : χ.comp pull = ρ := by
    refine AddMonoidHom.eq_of_eqOn_dense hgen ?_
    rintro _ ⟨u, rfl⟩
    exact congrArg Additive.ofMul (hgen_case u)
  have hx : χf (pull x) = ρf x := congrArg Additive.toMul (DFunLike.congr_fun heq x)

  have key : cls (h.poincare.pullbackAlong (pts (pull x))).L =
      cls (h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp (pts₀ x) deg)).L := by
    apply cls_eq_of_cls_pullback_eq eη
    rw [hρ x]
    exact hx
  exact congrArg Subtype.val (h.ext_of_iso _ (pts (pull x)) (NeronModelInfra.schemeHomOverComp (pts₀ x) deg)
    ((cls_eq_iff _ _).1 key))

end G

end PullPtsH
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_pts_alphaPull_eq_pts_levelN_comp_degPull.PullPtsH"

open PullPtsH in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hMeta₀π : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y))
    (hMeta₀πw : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y))
    (degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM)))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)

    (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
    (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
    (hajQ₀ε : (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ₀.1 = (D₀.baseChange ℚ).zeroSection)
    (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
      Nonempty ((hDQ₀.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ₀ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
    (hkQ₀₁ : kQ₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p))
    (hkQ₀₂ : kQ₀ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar₀ : Meta₀.C ⟶ D₀.P) (hajbar₀ : ajbar₀ = eeta₀ ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ))
    (hajbar₀_over : ajbar₀ ≫ D₀.toBase = Meta₀.toBase ≫ genPt p)
    (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1)
    (hεbar₀_aj : εbar₀.1 ≫ ajbar₀ = genPt p ≫ D₀.zeroSection)

    (pts₀ : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase)
    (hpts₀_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM),
      pts₀ (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (hpull0 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))
    :
    ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (pts (αpull i x)).1 = (pts₀ x).1 ≫ (degPull i).1 := by
  intro i x
  haveI := isCurveOver_xHFunctionFieldBar M H
  haveI := isCurveOver_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  haveI := essFiniteType_xHFunctionFieldBar M H
  haveI := essFiniteType_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  haveI := 𝔛.smooth_generic
  haveI := 𝔛.smooth0
  obtain ⟨hfinπ, hlfpπ, hflatπ, -⟩ := ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi p M H hpM hpM2 hHp hj 𝔛
  haveI := hfinπ
  haveI := hlfpπ
  haveI := hflatπ
  have hg : genPt p = tQ ≫ specMap (R p) ℚ := (specMap_comp_specMap (R p) ℚ ℚ̄).symm
  have hFIα := fundamentalIdentityAlong_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) M H αH hαint
  have hFIβ := fundamentalIdentityAlong_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) M H βH hβint
  fin_cases i
  ·
    exact pts_pull_eq_pts_comp (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) 𝔛.εinf
      (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) (genPt p) hg
      D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ 𝔛.Meta 𝔛.eeta 𝔛.heeta ajbar hajbar εbar hεbar pts hpts_add hpts_aj
      D₀ hD₀ hDQ₀ hPQ₀ ajQ₀ hajQ₀ kQ₀ hkQ₀₁ hkQ₀₂ Meta₀ eeta₀ heeta₀ ajbar₀ hajbar₀ εbar₀ hεbar₀ pts₀ hpts₀_add hpts₀_aj
      𝔛.π αH hαint hFIα hMeta₀π (αpull 0) hpull0 (degPull 0) (fun b => hdegPull 0 (genPt p) b) x
  ·
    haveI : IsFinite 𝔛.πw.1 := by
      change IsFinite (𝔛.w.hom ≫ 𝔛.π.1); infer_instance
    haveI : Flat 𝔛.πw.1 := by
      change Flat (𝔛.w.hom ≫ 𝔛.π.1); infer_instance
    haveI : LocallyOfFinitePresentation 𝔛.πw.1 := by
      change LocallyOfFinitePresentation (𝔛.w.hom ≫ 𝔛.π.1); infer_instance
    exact pts_pull_eq_pts_comp (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) 𝔛.εinf
      (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) (genPt p) hg
      D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ 𝔛.Meta 𝔛.eeta 𝔛.heeta ajbar hajbar εbar hεbar pts hpts_add hpts_aj
      D₀ hD₀ hDQ₀ hPQ₀ ajQ₀ hajQ₀ kQ₀ hkQ₀₁ hkQ₀₂ Meta₀ eeta₀ heeta₀ ajbar₀ hajbar₀ εbar₀ hεbar₀ pts₀ hpts₀_add hpts₀_aj
      𝔛.πw βH hβint hFIβ hMeta₀πw (αpull 1) hpull1 (degPull 1) (fun b => hdegPull 1 (genPt p) b) x

end
end S_ModularCurve_XHDRModelAtP_pts_alphaPull_eq_pts_levelN_comp_degPull
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_pts_alphaPull_eq_pts_levelN_comp_degPull (solution)
