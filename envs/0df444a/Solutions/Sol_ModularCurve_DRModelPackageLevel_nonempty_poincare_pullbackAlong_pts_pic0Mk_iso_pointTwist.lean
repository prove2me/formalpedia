-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7f4a5c0f-a857-5325-b3a5-be65e47b8f09

import Mathlib
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP"

noncomputable section

universe u v

namespace PrincTriv

def ClsMon (X : Scheme.{u}) : Type (u + 1) := Quotient (isIsomorphicSetoid X.Modules)

variable {X Y : Scheme.{u}}

def cls (A : X.Modules) : ClsMon X := Quotient.mk _ A

theorem cls_eq_iff {A B : X.Modules} : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

scoped instance : CommMonoid (ClsMon X) where
  mul := Quotient.map₂ (fun A B => A ⊗ B) (fun _ _ hA _ _ hB => ⟨hA.some ⊗ᵢ hB.some⟩)
  one := cls (𝟙_ X.Modules)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Quotient.sound ⟨α_ _ _ _⟩
  one_mul a := Quotient.inductionOn a fun _ => Quotient.sound ⟨λ_ _⟩
  mul_one a := Quotient.inductionOn a fun _ => Quotient.sound ⟨ρ_ _⟩
  mul_comm a b := Quotient.inductionOn₂ a b fun _ _ => Quotient.sound ⟨β_ _ _⟩

theorem cls_tensor (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B := rfl

theorem cls_unit : cls (𝟙_ X.Modules) = 1 := rfl

def unitOf (A B : X.Modules) (h : Nonempty (A ⊗ B ≅ 𝟙_ X.Modules)) : (ClsMon X)ˣ where
  val := cls A
  inv := cls B
  val_inv := by rw [← cls_tensor, ← cls_unit]; exact cls_eq_iff.mpr h
  inv_val := by rw [mul_comm, ← cls_tensor, ← cls_unit]; exact cls_eq_iff.mpr h

@[scoped simp] theorem val_unitOf (A B : X.Modules) (h) : (unitOf A B h : ClsMon X) = cls A := rfl
@[scoped simp] theorem inv_unitOf (A B : X.Modules) (h) : ((unitOf A B h)⁻¹ : (ClsMon X)ˣ) = (cls B : ClsMon X) := rfl

def pullbackCls (f : X ⟶ Y) : ClsMon Y →* ClsMon X where
  toFun := Quotient.map (fun A => (Scheme.Modules.pullback f).obj A) (fun _ _ h => ⟨(Scheme.Modules.pullback f).mapIso h.some⟩)
  map_one' := Quotient.sound ⟨Scheme.Modules.pullbackTensorUnitObjIso f⟩
  map_mul' a b := Quotient.inductionOn₂ a b fun A B => Quotient.sound ⟨Scheme.Modules.pullbackTensorObjIso f A B⟩

theorem pullbackCls_cls (f : X ⟶ Y) (A : Y.Modules) :
    pullbackCls f (cls A) = cls ((Scheme.Modules.pullback f).obj A) := rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist.PrincTriv"

namespace PrincTriv

variable {X Y : Scheme.{u}}

def idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) : (ClsMon X)ˣ :=
  unitOf I.module I.invModule hI.nonempty_module_tensor_invModule_iso.1

@[scoped simp] theorem val_idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (idealUnit I hI : ClsMon X) = cls I.module := rfl

@[scoped simp] theorem val_inv_idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) :
    ((idealUnit I hI)⁻¹ : (ClsMon X)ˣ) = (cls I.invModule : ClsMon X) := rfl

theorem idealUnit_congr {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    idealUnit I hI = idealUnit J hJ := by subst h; rfl

theorem idealUnit_mul {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIJ : (I * J).IsInvertible) : idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  ext
  show cls (I * J).module = cls I.module * cls J.module
  rw [← cls_tensor]
  obtain ⟨μ, -⟩ := hI.exists_tensor_iso_mul_module hJ
  exact (cls_eq_iff.mpr ⟨μ⟩).symm

theorem idealUnit_pow {I : X.IdealSheafData} (hI : I.IsInvertible) (k : ℕ) :
    idealUnit (I ^ k) (hI.pow k) = idealUnit I hI ^ k := by
  induction k with
  | zero =>
    have h00 : (I ^ 0 * I ^ 0).IsInvertible := by rw [← pow_add]; exact hI.pow 0
    have h2 : idealUnit (I ^ 0) (hI.pow 0) * idealUnit (I ^ 0) (hI.pow 0) = idealUnit (I ^ 0) (hI.pow 0) := by
      rw [← idealUnit_mul (hI.pow 0) (hI.pow 0) h00]
      exact idealUnit_congr _ _ (by rw [← pow_add])
    rw [show idealUnit I hI ^ 0 = 1 from pow_zero _]
    exact mul_left_cancel (h2.trans (mul_one _).symm)
  | succ k ih =>
    have h' : (I ^ k * I).IsInvertible := (pow_succ I k) ▸ hI.pow (k + 1)
    calc idealUnit (I ^ (k + 1)) (hI.pow (k + 1)) = idealUnit (I ^ k * I) h' := idealUnit_congr _ _ (pow_succ I k)
      _ = idealUnit (I ^ k) (hI.pow k) * idealUnit I hI := idealUnit_mul _ _ _
      _ = idealUnit I hI ^ (k + 1) := by rw [ih, pow_succ]

theorem cls_foldr {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (A B : Fin n → X.Modules) (l : List (Fin n)) :
    cls (l.foldr (fun i M => if c i = j then A i ⊗ B i ⊗ M else M) (𝟙_ X.Modules)) =
      (l.map fun i => if c i = j then cls (A i) * cls (B i) else 1).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    split_ifs with h
    · rw [cls_tensor, cls_tensor, ih, mul_assoc]
    · rw [ih, one_mul]

theorem cls_twist {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (I : Fin n → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ) :
    cls ((List.finRange n).foldr
        (fun i M => if c i = j then ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M else M)
        (𝟙_ X.Modules)) =
      ↑((∏ i ∈ Finset.univ.filter (fun i => c i = j), idealUnit (I i) (hI i) ^ ((pos i : ℤ) - (neg i : ℤ)))⁻¹) := by
  rw [cls_foldr c j (fun i => ((I i) ^ (pos i)).invModule) (fun i => ((I i) ^ (neg i)).module),
    ← Fin.prod_univ_def, ← Finset.prod_filter, ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show cls (((I i) ^ (pos i)).invModule) = ↑((idealUnit _ ((hI i).pow (pos i)))⁻¹) from rfl,
    show cls (((I i) ^ (neg i)).module) = ↑(idealUnit _ ((hI i).pow (neg i))) from rfl,
    idealUnit_pow, idealUnit_pow, ← Units.val_mul, ← zpow_neg, neg_sub, zpow_sub, zpow_natCast, zpow_natCast,
    mul_comm]

theorem prod_inv_mul_zpow {ι G : Type*} [CommGroup G] [DecidableEq ι] (s : Finset ι) (a : ι → G) (b : G) (m : ι → ℤ) :
    ∏ i ∈ s, ((a i)⁻¹ * b) ^ (m i) = (∏ i ∈ s, (a i) ^ (m i))⁻¹ * b ^ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih, mul_zpow, inv_zpow, zpow_add, mul_inv]
    ac_rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist.PrincTriv"

namespace PrincTriv
variable {X : Scheme.{u}}

theorem cls_foldr' {n : ℕ} (A B : Fin n → X.Modules) (l : List (Fin n)) :
    cls (l.foldr (fun i M => A i ⊗ B i ⊗ M) (𝟙_ X.Modules)) = (l.map fun i => cls (A i) * cls (B i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, List.map_cons, List.prod_cons]; rw [cls_tensor, cls_tensor, ih, mul_assoc]

theorem cls_twist' {n : ℕ} (I : Fin n → X.IdealSheafData) (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ) :
    cls ((List.finRange n).foldr
        (fun i M => ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M) (𝟙_ X.Modules)) =
      ↑((∏ i, idealUnit (I i) (hI i) ^ ((pos i : ℤ) - (neg i : ℤ)))⁻¹) := by
  rw [cls_foldr' (fun i => ((I i) ^ (pos i)).invModule) (fun i => ((I i) ^ (neg i)).module), ← Fin.prod_univ_def,
    ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show cls (((I i) ^ (pos i)).invModule) = ↑((idealUnit _ ((hI i).pow (pos i)))⁻¹) from rfl,
    show cls (((I i) ^ (neg i)).module) = ↑(idealUnit _ ((hI i).pow (neg i))) from rfl,
    idealUnit_pow, idealUnit_pow, ← Units.val_mul, ← zpow_neg, neg_sub, zpow_sub, zpow_natCast, zpow_natCast,
    mul_comm]

theorem idealUnit_congr' {I J : X.IdealSheafData} (hI : I.IsInvertible) (h : I = J) :
    idealUnit I hI = idealUnit J (h ▸ hI) := by subst h; rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist.PrincTriv"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    {n : ℕ} (q : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (x : Fin n → SchemeHomOver (genPt p) (toBase N₀ p))
    (hxq : ∀ i, (x i).1 = (q i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))

    (pos neg : Fin n → ℕ) (hn : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0)
    (Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
    (hDx : (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (q i)) ((pos i : ℤ) - (neg i : ℤ))) :
    Nonempty ((hD.poincare.pullbackAlong (pts (Pic0.mk Dx))).L ≅
      ((List.finRange n).foldr
          (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ M)
          (𝟙_ (pullback (toBase N₀ p) (genPt p)).Modules))) := by
  classical

  haveI := 𝔓.eeta_iso
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) (genPt p)) := by
    rw [show pullback.snd (toBase N₀ p) (genPt p) = inv 𝔓.eeta ≫ 𝔓.Meta.toBase by rw [IsIso.eq_inv_comp, 𝔓.heeta]]
    exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  have hIx : ∀ z : SchemeHomOver (genPt p) (toBase N₀ p),
      (RelEffCartierDiv.ofPoint (toBase N₀ p) z.1 z.2).I.IsInvertible := fun z =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase N₀ p) (genPt p))
      (graphOver (toBase N₀ p) z.1 z.2) (graphOver_snd _ _ _)

  let xe : SchemeHomOver (genPt p) (toBase N₀ p) :=
    ⟨genPt p ≫ 𝔓.εinf.1, by rw [Category.assoc, 𝔓.εinf.2, Category.comp_id]⟩
  let xof : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} →
      SchemeHomOver (genPt p) (toBase N₀ p) := fun y =>
    ⟨y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p), by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta, ← Category.assoc, y.2,
        Category.id_comp]⟩

  choose Dv hDv hpts using fun y => hpts_aj y εbar hεbar

  let Φf : JZero (N₀ * p) → PrincTriv.ClsMon (pullback (toBase N₀ p) (genPt p)) :=
    fun Q => PrincTriv.cls (hD.poincare.pullbackAlong (pts Q)).L
  have hmul : ∀ Q Q' : JZero (N₀ * p), Φf (Q + Q') = Φf Q * Φf Q' := fun Q Q' => by
    show PrincTriv.cls _ = PrincTriv.cls _ * PrincTriv.cls _
    rw [hpts_add, ← PrincTriv.cls_tensor]
    exact PrincTriv.cls_eq_iff.mpr (RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso
      (P := algEquivZeroGroupCut (toBase N₀ p) 𝔓.εinf) hD (genPt p) (pts Q) (pts Q'))

  have hover : ∀ y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _},
      (y.1 ≫ ajbar) ≫ D.toBase = genPt p := fun y => by
    rw [Category.assoc, hajbar_over, ← Category.assoc, y.2, Category.id_comp]
  have hval : ∀ y, Φf (Pic0.mk (Dv y)) =
      ↑((PrincTriv.idealUnit _ (hIx (xof y)))⁻¹ * PrincTriv.idealUnit _ (hIx xe)) := by
    intro y
    have hq : pts (Pic0.mk (Dv y)) = ⟨y.1 ≫ ajbar, hover y⟩ := Subtype.ext (hpts y)
    show PrincTriv.cls _ = _
    rw [hq, Units.val_mul, PrincTriv.val_inv_idealUnit, PrincTriv.val_idealUnit, ← PrincTriv.cls_tensor]
    exact PrincTriv.cls_eq_iff.mpr
      (ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
        N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ ajbar hajbar y (xof y) rfl ⟨y.1 ≫ ajbar, hover y⟩ rfl)

  have hone : Φf 0 = 1 := by
    have hz0 : Pic0.mk (Dv εbar) = 0 := by
      rw [← Pic0.mk_zero]
      congr 1
      apply Subtype.ext
      rw [hDv]
      exact sub_self _
    have h2 : Φf 0 * Φf 0 = Φf 0 := by rw [← hmul, add_zero]
    rw [← hz0, hval εbar, ← Units.val_mul, Units.val_inj] at h2
    rw [← hz0, hval εbar, mul_left_cancel (h2.trans (mul_one _).symm), Units.val_one]
  let Φ : Multiplicative (JZero (N₀ * p)) →* PrincTriv.ClsMon (pullback (toBase N₀ p) (genPt p)) :=
    { toFun := fun Q => Φf Q.toAdd, map_one' := hone, map_mul' := fun Q Q' => hmul Q.toAdd Q'.toAdd }
  have hΦ : ∀ i, Φ.toHomUnits (Multiplicative.ofAdd (Pic0.mk (Dv (q i)))) =
      (PrincTriv.idealUnit _ (hIx (xof (q i))))⁻¹ * PrincTriv.idealUnit _ (hIx xe) := fun i => Units.ext (hval (q i))

  have hDsum : Dx = ∑ i, ((pos i : ℤ) - (neg i : ℤ)) • Dv (q i) := by
    apply Subtype.ext
    have hterm : ∀ i, ((((pos i : ℤ) - (neg i : ℤ)) • Dv (q i) :
        ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p))))) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) =
        Finsupp.single (𝔓.Meta.pointEquivPlace (q i)) ((pos i : ℤ) - (neg i : ℤ)) -
          ((pos i : ℤ) - (neg i : ℤ)) • Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1 := by
      intro i
      rw [AddSubgroupClass.coe_zsmul, hDv, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hDx, AddSubmonoidClass.coe_finsetSum, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hn, zero_smul, sub_zero]
  have hmk : Pic0.mk Dx = ∑ i, ((pos i : ℤ) - (neg i : ℤ)) • Pic0.mk (Dv (q i)) := by
    change (QuotientAddGroup.mk' _) Dx = ∑ i, ((pos i : ℤ) - (neg i : ℤ)) • (QuotientAddGroup.mk' _) (Dv (q i))
    rw [hDsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _

  have key : PrincTriv.cls (hD.poincare.pullbackAlong (pts (Pic0.mk Dx))).L =
      ↑((∏ i, PrincTriv.idealUnit _ (hIx (xof (q i))) ^ ((pos i : ℤ) - (neg i : ℤ)))⁻¹) := by
    have e1 : PrincTriv.cls (hD.poincare.pullbackAlong (pts (Pic0.mk Dx))).L =
        ↑(Φ.toHomUnits (Multiplicative.ofAdd (Pic0.mk Dx))) := rfl
    rw [e1, hmk, ofAdd_sum, map_prod]
    simp_rw [ofAdd_zsmul, map_zpow, hΦ]
    rw [PrincTriv.prod_inv_mul_zpow, hn, zpow_zero, mul_one]

  have hxx : ∀ i, x i = xof (q i) := fun i => Subtype.ext (hxq i)
  rw [PrincTriv.cls_eq_iff.symm, key,
    PrincTriv.cls_twist' (fun i => (RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I) (fun i => hIx (x i)) pos neg]
  congr 3
  funext i
  rw [hxx i]

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist.PrincTriv"

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist (solution)
