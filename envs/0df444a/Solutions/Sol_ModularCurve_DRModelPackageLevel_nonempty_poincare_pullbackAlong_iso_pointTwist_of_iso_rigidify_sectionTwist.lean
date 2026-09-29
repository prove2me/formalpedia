-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3d3498d2-ae7d-5deb-916b-f311323e3dda

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
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

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.PrincTriv"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.PrincTriv"

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
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.PrincTriv"

namespace PrincTriv
variable {X : Scheme.{u}}

theorem isInvertible_twist {n : ℕ} (I : Fin n → X.IdealSheafData) (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ)
    (l : List (Fin n)) :
    Scheme.Modules.IsInvertible (l.foldr
      (fun i M => ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M) (𝟙_ X.Modules)) := by
  induction l with
  | nil => exact Scheme.Modules.isInvertible_unit X
  | cons i l ih =>
    rw [List.foldr_cons]
    exact ((hI i).pow (pos i)).isInvertible_invModule.tensor (((hI i).pow (neg i)).isInvertible_module.tensor ih)

theorem nonempty_iso_unit_of_field {K : Type u} [Field K] (M : (Spec (CommRingCat.of K)).Modules)
    (hM : Scheme.Modules.IsInvertible M) : Nonempty (M ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization (IsLocalRing.closedPoint K)
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hU : U = ⊤ := eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]; exact hxU
  subst hU
  exact ⟨((Scheme.Modules.pullbackId _).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr (Spec (CommRingCat.of K)).topIso.inv_hom_id.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _⟩

theorem map_pullbackCls_idealUnit_of_comap {Y : Scheme.{u}} (g : Y ⟶ X) {I : X.IdealSheafData} {J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I.comap g = J) :
    Units.map (pullbackCls g : ClsMon X →* ClsMon Y) (idealUnit I hI) = idealUnit J hJ := by
  subst h
  rw [← inv_inj, ← map_inv]
  ext
  show pullbackCls g (cls I.invModule) = cls (I.comap g).invModule
  rw [pullbackCls_cls]
  exact cls_eq_iff.mpr (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso g hI hJ)

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.PrincTriv"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
    (hsm : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)))

    (x : Fin n → SchemeHomOver (genPt p) (toBase N₀ p))
    (hx : ∀ i, (x i).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ (s i).1)
    (pos neg : Fin n → ℕ)

    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (ha : Nonempty ((hD.poincare.pullbackAlong a).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
          (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)))
          ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))

    (b : SchemeHomOver (genPt p) D.toBase) (hb : b.1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ a.1) :
    Nonempty ((hD.poincare.pullbackAlong b).L ≅
      ((List.finRange n).foldr
          (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ M)
          (𝟙_ (pullback (toBase N₀ p) (genPt p)).Modules))) := by
  classical

  have hgen : Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) = genPt p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ)),
      ψ = ⟨Spec.map (CommRingCat.ofHom A.subtype), hgen⟩ := ⟨_, rfl⟩
  have hbψ : b = postComp a ψ := Subtype.ext (by rw [hψ]; exact hb)

  haveI := 𝔓.eeta_iso
  haveI hsmη : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) (genPt p)) := by
    rw [show pullback.snd (toBase N₀ p) (genPt p) = inv 𝔓.eeta ≫ 𝔓.Meta.toBase by rw [IsIso.eq_inv_comp, 𝔓.heeta]]
    exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hIx : ∀ z : SchemeHomOver (genPt p) (toBase N₀ p),
      (RelEffCartierDiv.ofPoint (toBase N₀ p) z.1 z.2).I.IsInvertible := fun z =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase N₀ p) (genPt p))
      (graphOver (toBase N₀ p) z.1 z.2) (graphOver_snd _ _ _)

  have hIs : ∀ i, (RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I.IsInvertible := fun i =>
    RelEffCartierDiv.isInvertible_I_of_supportedIn 𝔓.smoothLocus _
      (RelEffCartierDiv.supportedIn_ofPoint _ _ _ fun t => hsm i ⟨t, rfl⟩)

  have hcomap : ∀ i, (RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I.comap (baseChangeSnd (toBase N₀ p) ψ) =
      (RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I := by
    intro i
    have hxi : x i = ⟨ψ.1 ≫ (s i).1, by rw [Category.assoc, (s i).2, ψ.2]⟩ := Subtype.ext (by rw [hx i, hψ])
    rw [hxi]
    exact congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint (toBase N₀ p) (s i).1 (s i).2 ψ.1 ψ.2)
  have htr : ∀ i, Units.map (PrincTriv.pullbackCls (baseChangeSnd (toBase N₀ p) ψ) : PrincTriv.ClsMon _ →* PrincTriv.ClsMon _)
      (PrincTriv.idealUnit _ (hIs i)) = PrincTriv.idealUnit _ (hIx (x i)) := fun i =>
    PrincTriv.map_pullbackCls_idealUnit_of_comap _ (hIs i) (hIx (x i)) (hcomap i)

  have hF := PrincTriv.isInvertible_twist (fun i => (RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I) hIs pos neg
    (List.finRange n)
  have hTW := PrincTriv.isInvertible_twist (fun i => (RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I)
    (fun i => hIx (x i)) pos neg (List.finRange n)
  have eF : Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψ)).obj ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules)) ≅
      ((List.finRange n).foldr
          (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ M)
          (𝟙_ (pullback (toBase N₀ p) (genPt p)).Modules))) := by
    apply PrincTriv.cls_eq_iff.mp
    rw [← PrincTriv.pullbackCls_cls, PrincTriv.cls_twist' _ hIs, PrincTriv.cls_twist' _ (fun i => hIx (x i)),
      ← Units.coe_map, map_inv, map_prod]
    simp_rw [map_zpow, htr]

  obtain ⟨erig⟩ := PrincTriv.nonempty_iso_unit_of_field _ (hTW.pullback (rigSection (toBase N₀ p) (genPt p) 𝔓.εinf))
  let Mx : RigidifiedLineBundle (toBase N₀ p) 𝔓.εinf (genPt p) := ⟨_, hTW, ⟨erig⟩⟩

  obtain ⟨e0⟩ := ha
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := 𝔓.εinf) ψ hF
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := 𝔓.εinf) (hF.pullback _) hTW eF.some
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified Mx
  rw [hbψ]
  exact ⟨(hD.poincare.pullbackAlongPullbackAlongIso' a ψ).symm ≪≫ (Scheme.Modules.pullback _).mapIso e0 ≪≫ e1 ≪≫ e2 ≪≫ e3⟩

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.PrincTriv"

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist (solution)
