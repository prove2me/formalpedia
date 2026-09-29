-- Prove2me | solution 1 for ModularCurve.DRModelPackage.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/992c3c94-5bb9-5a08-8883-d3f574f94222

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
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization
open Opposite
open scoped CategoryTheory.MonObj

universe u

noncomputable section

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
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso.K6Kit"

namespace K6Kit

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

set_option maxHeartbeats 1600000 in
theorem poincare_aj
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (aj : 𝔛.Mη.C ⟶ D.P)
    [IsProper (DRModel.toBase p)]
    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ))
    (hk₁ : k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)))
    (hk₂ : k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
          pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajk : aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ))
    (w : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (hw : (w.1 ≫ aj) ≫ D.toBase = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hxw : (w.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) ≫ DRModel.toBase p =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hε : (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1) ≫ DRModel.toBase p =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) :
    Nonempty ((hD.poincare.pullbackAlong ⟨w.1 ≫ aj, hw⟩).L ≅
      (RelEffCartierDiv.ofPoint (DRModel.toBase p) (w.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) hxw).lineBundle ⊗
      (RelEffCartierDiv.ofPoint (DRModel.toBase p)
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1) hε).idealModule) := by
  haveI := 𝔛.eη_iso

  let Qb := AlgebraicClosure ℚ
  let c := DRModel.toBase p
  let c' := baseChange ℤ (DRModel.toBase p) ℚ
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb))
  let sQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ℚ) := Spec.map (CommRingCat.ofHom (algebraMap ℚ Qb))
  have hsX : tQ = sQ ≫ specMap ℤ ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  let y : Spec (CommRingCat.of Qb) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ) := w.1 ≫ 𝔛.eη ≫ k₀
  have hy : y ≫ c' = sQ := by
    show (w.1 ≫ 𝔛.eη ≫ k₀) ≫ pullback.snd _ _ = _
    rw [Category.assoc, Category.assoc, hk₂, reassoc_of% 𝔛.heη, ← Category.assoc, w.2, Category.id_comp]
  let xQ : SchemeHomOver sQ c' := ⟨y, hy⟩
  obtain ⟨i2⟩ := hajQ Qb sQ xQ

  let κ' : pullback c' sQ ≅ pullback c tQ := BaseChange.κ c ℚ sQ ≪≫ pullback.congrHom rfl hsX.symm
  have hκ'1 : κ'.hom ≫ pullback.fst c tQ = pullback.fst c' sQ ≫ pullback.fst c (specMap ℤ ℚ) := by
    simp only [κ', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
    exact BaseChange.κ_hom_fst c ℚ sQ
  have hκ'2 : κ'.hom ≫ pullback.snd c tQ = pullback.snd c' sQ := by
    simp only [κ', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
    exact BaseChange.κ_hom_snd c ℚ sQ

  let tD' := (D.baseChange ℚ).toBase
  let φD : SchemeHomOver (tD' ≫ specMap ℤ ℚ) D.toBase := ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩
  let ψ : SchemeHomOver sQ tD' := ⟨xQ.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (xQ.1 ≫ ·) ajQ.2).trans xQ.2)⟩
  let g : SchemeHomOver tQ D.toBase := ⟨w.1 ≫ aj, hw⟩
  have E : (baseChangeSnd c' ψ ≫ (BaseChange.κ c ℚ tD').hom) ≫ baseChangeSnd c φD = κ'.hom ≫ baseChangeSnd c g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, ← Category.assoc,
        BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst', hκ'1]
    · show ((baseChangeSnd c' ψ ≫ (BaseChange.κ c ℚ tD').hom) ≫ baseChangeSnd c φD) ≫ pullback.snd c D.toBase =
        (κ'.hom ≫ baseChangeSnd c g) ≫ pullback.snd c D.toBase
      simp only [Category.assoc, BaseChange.baseChangeSnd_snd']
      rw [reassoc_of% (BaseChange.κ_hom_snd c ℚ tD'), reassoc_of% (BaseChange.baseChangeSnd_snd' ℚ c' ψ), reassoc_of% hκ'2]
      show pullback.snd c' sQ ≫ ((w.1 ≫ 𝔛.eη ≫ k₀) ≫ ajQ.1) ≫ pullback.fst D.toBase (specMap ℤ ℚ) =
        pullback.snd c' sQ ≫ w.1 ≫ aj
      rw [hajk]
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

  have hp : graphOver c (w.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) hxw ≫ κ'.inv = graphOver c' y hy := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, hκ'1, graphOver_fst_assoc, graphOver_fst]
      show _ = (w.1 ≫ 𝔛.eη ≫ k₀) ≫ _
      rw [Category.assoc, Category.assoc, hk₁]
    · rw [Category.assoc, hκ'2, graphOver_snd, graphOver_snd]
  have hpε : graphOver c (tQ ≫ 𝔛.εinf.1) hε ≫ κ'.inv =
      graphOver c' (sQ ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (sQ ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans (Category.comp_id sQ))) := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, hκ'1, graphOver_fst_assoc, graphOver_fst, Category.assoc, sectionBaseChange_coe_fst,
        ← Category.assoc, ← hsX]
    · rw [Category.assoc, hκ'2, graphOver_snd, graphOver_snd]

  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd c tQ) :=
    smoothOfRelativeDimension_one_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη) (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])
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

end K6Kit
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso.K6Kit"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso.K6Kit"

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime]
    (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (aj : 𝔛.Mη.C ⟶ D.P)
    [IsProper (DRModel.toBase p)]
    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (hk₀ : ∃ k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ),
        k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ∧
        k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
          pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ))
    (haj_over : aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))
    (pts_aj : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj)

    (O : Type) [CommRing O] (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) D.toBase)
    (tb : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of O))
    (htb : tb ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (m : ℕ) (q : Fin m → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (pos neg : Fin m → ℕ) (hn : (∑ j, ((pos j : ℤ) - (neg j : ℤ))) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p))))
    (hDxq : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
      ∑ j, Finsupp.single (𝔛.Mη.pointEquivPlace (q j)) ((pos j : ℤ) - (neg j : ℤ)))
    (hzgen : Nonempty ((hD.poincare.pullbackAlong ⟨tb ≫ z.1, by rw [Category.assoc, z.2, htb]⟩).L ≅
      (List.finRange m).foldr (fun j M =>
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (neg j)).module ⊗ M)
        (𝟙_ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).Modules))) :
    (pts (Pic0.mk Dx)).1 = tb ≫ z.1 := by
  classical
  haveI := 𝔛.eη_iso

  let Qb := AlgebraicClosure ℚ
  let c := DRModel.toBase p
  let ε := 𝔛.εinf
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb))
  let Pg := algEquivZeroGroupCut c ε
  letI := (RepresentsRelSubPic.relativeGroupLaw (P := Pg) hD).pointGroup tQ
  obtain ⟨k₀, hk₁, hk₂, hajk⟩ := hk₀

  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd c tQ) :=
    K6Kit.smoothOfRelativeDimension_one_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη)
      (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])

  have hx : ∀ j, ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) ≫ DRModel.toBase p = tQ := fun j => by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2]
  have hε : (tQ ≫ ε.1) ≫ c = tQ := (Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _))
  let I : Fin m → (pullback c tQ).IdealSheafData := fun j =>
    (RelEffCartierDiv.ofPoint c ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I
  let Iε : (pullback c tQ).IdealSheafData := (RelEffCartierDiv.ofPoint c (tQ ≫ ε.1) hε).I
  have hI : ∀ j, (I j).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tQ) _ (graphOver_snd _ _ _)
  have hIε : Iε.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tQ) _ (graphOver_snd _ _ _)

  let O : Fin m → K6Kit.Cl c ε tQ := fun j => K6Kit.clI ε tQ (I j) (hI j)
  let E : K6Kit.Cl c ε tQ := K6Kit.clM ε tQ Iε hIε
  let Φ : JZero p →+ Additive (K6Kit.Cl c ε tQ) :=
    { toFun := fun x => Additive.ofMul (K6Kit.pcl (P := Pg) hD (pts x))
      map_zero' := by
        apply congrArg Additive.ofMul
        apply K6Kit.cl_eq_one_of_mul_self
        show K6Kit.pcl (P := Pg) hD (pts 0) * K6Kit.pcl (P := Pg) hD (pts 0) = K6Kit.pcl (P := Pg) hD (pts 0)
        have h00 := K6Kit.pcl_mul (P := Pg) hD tQ (pts 0) (pts 0)
        rw [← pts_add, add_zero] at h00
        exact h00.symm
      map_add' := fun x y => by
        show Additive.ofMul (K6Kit.pcl (P := Pg) hD (pts (x + y))) = Additive.ofMul (K6Kit.pcl (P := Pg) hD (pts x)) + Additive.ofMul (K6Kit.pcl (P := Pg) hD (pts y))
        rw [pts_add]
        exact congrArg Additive.ofMul (K6Kit.pcl_mul (P := Pg) hD tQ (pts x) (pts y)) }

  choose Dv hDv hptsDv using fun j => pts_aj (q j)
  have hw : ∀ j, ((q j).1 ≫ aj) ≫ D.toBase = tQ := fun j => by
    rw [Category.assoc, haj_over, ← Category.assoc, (q j).2, Category.id_comp]
  have step1 : ∀ j, Φ (Pic0.mk (Dv j)) = Additive.ofMul (O j) + Additive.ofMul E := by
    intro j
    show Additive.ofMul (K6Kit.pcl (P := Pg) hD (pts (Pic0.mk (Dv j)))) = _
    rw [← ofMul_mul]
    apply congrArg Additive.ofMul
    have hpt : pts (Pic0.mk (Dv j)) = ⟨(q j).1 ≫ aj, hw j⟩ := Subtype.ext (hptsDv j)
    rw [hpt]
    unfold K6Kit.pcl
    rw [← K6Kit.cl_rig_L]
    have hF := K6Kit.poincare_aj p 𝔛 D hD aj h' ajQ hP hajQ k₀ hk₁ hk₂ hajk (q j) (hw j) (hx j) hε
    exact (K6Kit.cl_rig_congr (ε := ε) _ ((hI j).isInvertible_invModule.tensor hIε.isInvertible_module) hF).trans
      (K6Kit.cl_rig_tensor (ε := ε) _ _)

  let mkHom : ↥(Divisor.degZero (K := Qb) (F := ↥(modularFunctionFieldBar p))) →+ JZero p :=
    { toFun := Pic0.mk, map_zero' := Pic0.mk_zero, map_add' := Pic0.mk_add }
  have h1 : Dx = ∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Dv j := by
    apply Subtype.ext
    rw [hDxq, AddSubgroup.val_finsetSum]
    simp only [AddSubgroupClass.coe_zsmul, hDv, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, ← Finsupp.single_finsetSum, hn, Finsupp.single_zero, sub_zero]
  have hDx : Pic0.mk Dx = ∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Pic0.mk (Dv j) := by
    show mkHom Dx = ∑ j, ((pos j : ℤ) - (neg j : ℤ)) • mkHom (Dv j)
    rw [h1, map_sum]
    simp only [map_zsmul]
  have hL : Φ (Pic0.mk Dx) = ∑ j, ((pos j : ℤ) - (neg j : ℤ)) • Additive.ofMul (O j) := by
    rw [hDx, map_sum]
    simp only [map_zsmul, step1, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hn, zero_smul, add_zero]
  have hL' : K6Kit.pcl (P := Pg) hD (pts (Pic0.mk Dx)) = ∏ j, O j ^ ((pos j : ℤ) - (neg j : ℤ)) := by
    have := congrArg Additive.toMul hL
    simp only [toMul_ofMul, toMul_sum, toMul_zsmul] at this
    exact this

  let zb : SchemeHomOver tQ D.toBase := ⟨tb ≫ z.1, by rw [Category.assoc, z.2, htb]⟩
  let F : Fin m → (pullback c tQ).Modules → (pullback c tQ).Modules := fun j M =>
    ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module ⊗ M
  have hFinv : ∀ l : List (Fin m), Scheme.Modules.IsInvertible (l.foldr F (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact Scheme.Modules.isInvertible_unit _
    | cons j l ih => exact ((hI j).pow (pos j)).isInvertible_invModule.tensor (((hI j).pow (neg j)).isInvertible_module.tensor ih)
  have hFcl : ∀ l : List (Fin m), K6Kit.cl (K6Kit.rig ε tQ (l.foldr F (𝟙_ _)) (hFinv l)) =
      (l.map fun j => K6Kit.clI ε tQ ((I j) ^ (pos j)) ((hI j).pow _) * K6Kit.clM ε tQ ((I j) ^ (neg j)) ((hI j).pow _)).prod := by
    intro l
    induction l with
    | nil => exact K6Kit.cl_rig_unit' _
    | cons j l ih =>
      rw [List.map_cons, List.prod_cons, ← ih, mul_assoc]
      exact (K6Kit.cl_rig_tensor' (ε := ε) ((hI j).pow (pos j)).isInvertible_invModule
          (((hI j).pow (neg j)).isInvertible_module.tensor (hFinv l)) _).trans
        (congrArg _ (K6Kit.cl_rig_tensor' (ε := ε) ((hI j).pow (neg j)).isInvertible_module (hFinv l) _))
  have hR : K6Kit.pcl (P := Pg) hD zb = ∏ j, O j ^ ((pos j : ℤ) - (neg j : ℤ)) := by
    unfold K6Kit.pcl
    rw [← K6Kit.cl_rig_L]
    have e1 : K6Kit.cl (K6Kit.rig ε tQ (hD.poincare.pullbackAlong zb).L (hD.poincare.pullbackAlong zb).isInvertible) =
        K6Kit.cl (K6Kit.rig ε tQ ((List.finRange m).foldr F (𝟙_ _)) (hFinv (List.finRange m))) :=
      K6Kit.cl_rig_congr (ε := ε) _ _ hzgen
    rw [e1, hFcl, ← Fin.prod_univ_def]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [K6Kit.clI_pow (hI j), K6Kit.clM_pow (hI j), K6Kit.clM_eq_inv (hI j)]
    show O j ^ pos j * (O j)⁻¹ ^ neg j = O j ^ ((pos j : ℤ) - (neg j : ℤ))
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add, sub_eq_add_neg]

  have key : pts (Pic0.mk Dx) = zb := K6Kit.pcl_injective (P := Pg) hD tQ (hL'.trans hR.symm)
  exact congrArg Subtype.val key

end S_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso (solution)
