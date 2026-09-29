-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_obj_of_comp_fst_eq_frobenius_comp_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c77e04f2-1276-53a8-a7a5-c68042ed68e2

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel

import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_obj_of_comp_fst_eq_frobenius_comp_twoChartModel_x1_mul
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u

namespace CpHelp

noncomputable def isoOfPullbackIso' {P Q : Scheme.{u}} (φ : Q ⟶ P) [IsIso φ] {A B : P.Modules}
    (i : (Scheme.Modules.pullback φ).obj A ≅ (Scheme.Modules.pullback φ).obj B) : A ≅ B :=
  ((Scheme.Modules.pullbackId P).app A).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ).symm).app A ≪≫
    ((Scheme.Modules.pullbackComp (inv φ) φ).app A).symm ≪≫
    (Scheme.Modules.pullback (inv φ)).mapIso i ≪≫
    (Scheme.Modules.pullbackComp (inv φ) φ).app B ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app B ≪≫
    (Scheme.Modules.pullbackId P).app B

theorem nonempty_rigidify_iso_self' {k : Type u} [Field k] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of k) ⟶ P) (q : P ⟶ Spec (CommRingCat.of k)) (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨i⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible σ q L hL k (𝟙 _)
  exact ⟨isoOfPullbackIso' (pullback.fst q (𝟙 _)) i⟩

end CpHelp

namespace TwistBC

theorem transport
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR cX ε k
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    (w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (aw : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) D.toBase)
    (haw : aw.1 = w.1 ≫ pullback.fst D.toBase (specMap R k)) :
    Nonempty ((hreps.poincare.pullbackAlong w).L ≅
      (Scheme.Modules.pullback ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX aw)).obj hrep.poincare.L) := by
  let ā : SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase :=
    ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩
  have hcomp : baseChangeSnd (baseChange R cX k) w ≫ (BaseChange.κ cX k (D.baseChange k).toBase).hom ≫ baseChangeSnd cX ā =
      (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX aw := by
    rw [← Category.assoc, BaseChange.baseChangeSnd_κ_hom, Category.assoc, baseChangeSnd_comp]
    congr 2
    apply Subtype.ext
    show w.1 ≫ pullback.fst D.toBase (specMap R k) = aw.1
    exact haw.symm
  exact ⟨(Scheme.Modules.pullback (baseChangeSnd (baseChange R cX k) w)).mapIso hPk.some ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX k) w)).mapIso
        ((Scheme.Modules.pullbackComp (BaseChange.κ cX k (D.baseChange k).toBase).hom (baseChangeSnd cX ā)).app hrep.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hrep.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app hrep.poincare.L⟩

private theorem _root_.TwistBC.generic
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR cX ε k
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ specMap R k = specMap R k)
    (F : pullback cX (specMap R k) ⟶ pullback cX (specMap R k))
    (hF₁ : F ≫ pullback.fst cX (specMap R k) = pullback.fst cX (specMap R k))
    (hF₂ : F ≫ pullback.snd cX (specMap R k) = pullback.snd cX (specMap R k) ≫ φ)
    (Fk : pullback (baseChange R cX k) (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback (baseChange R cX k) (𝟙 (Spec (CommRingCat.of k))))
    (hFk₁ : Fk ≫ pullback.fst (baseChange R cX k) (𝟙 _) = pullback.fst (baseChange R cX k) (𝟙 _) ≫ F)
    (hFk₂ : Fk ≫ pullback.snd (baseChange R cX k) (𝟙 _) = pullback.snd (baseChange R cX k) (𝟙 _) ≫ φ)
    (v v' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hv : v'.1 ≫ pullback.fst D.toBase (specMap R k) = φ ≫ v.1 ≫ pullback.fst D.toBase (specMap R k)) :
    Nonempty ((hreps.poincare.pullbackAlong v').L ≅ (Scheme.Modules.pullback Fk).obj (hreps.poincare.pullbackAlong v).L) := by

  have hbase : ∀ (w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
      (w.1 ≫ pullback.fst D.toBase (specMap R k)) ≫ D.toBase = 𝟙 _ ≫ specMap R k := by
    intro w
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ specMap R k) w.2
  let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) D.toBase := ⟨v.1 ≫ pullback.fst D.toBase (specMap R k), hbase v⟩
  let a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) D.toBase := ⟨v'.1 ≫ pullback.fst D.toBase (specMap R k), hbase v'⟩
  let ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) :=
    ⟨φ, by rw [Category.id_comp, hφ]⟩
  have ha' : a' = postComp a ψ := by
    apply Subtype.ext
    show v'.1 ≫ pullback.fst D.toBase (specMap R k) = φ ≫ v.1 ≫ pullback.fst D.toBase (specMap R k)
    exact hv
  obtain ⟨ev⟩ := transport cX ε D hrep k hreps hPk v a rfl
  obtain ⟨ev'⟩ := transport cX ε D hrep k hreps hPk v' a' rfl

  have hkey : Fk ≫ (BaseChange.κ cX k (𝟙 _)).hom = (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ := by
    apply pullback.hom_ext
    · rw [Category.assoc, BaseChange.κ_hom_fst, ← Category.assoc, hFk₁, Category.assoc, hF₁, Category.assoc,
        BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst]
    · rw [Category.assoc, BaseChange.κ_hom_snd, hFk₂, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc,
        BaseChange.κ_hom_snd]
  have hmor : (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX a' = Fk ≫ (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX a := by
    rw [ha', ← baseChangeSnd_comp, ← Category.assoc, ← hkey, Category.assoc]
  exact ⟨ev' ≪≫ (Scheme.Modules.pullbackCongr hmor).app hrep.poincare.L ≪≫
    ((Scheme.Modules.pullbackComp Fk ((BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX a)).app hrep.poincare.L).symm ≪≫
    (Scheme.Modules.pullback Fk).mapIso ev.symm⟩

p2m_export "TwistBC" "generic"
end TwistBC

namespace Compat1

open CpHelp

theorem restrict
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    {C₁ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (i₁ : SchemeHomOver c₁ (baseChange R cX k))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase) :
    Nonempty ((hrep₁.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) w)).L ≅
      (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong w).L) := by
  obtain ⟨e1⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
    i₁.1 i₁.2 hε₁ hreps hrep₁ (𝟙 _) w
  have e1' : (hrep₁.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) w)).L ≅
      Scheme.Modules.rigidify (rigSection c₁ (𝟙 _) ε₁) (pullback.snd c₁ (𝟙 _))
        ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong w).L) := e1
  obtain ⟨e2⟩ := nonempty_rigidify_iso_self' (rigSection c₁ (𝟙 _) ε₁) (pullback.snd c₁ (𝟙 _)) _
    ((hreps.poincare.pullbackAlong w).isInvertible.pullback (curveChange i₁.1 i₁.2 (𝟙 _)))
  exact ⟨e1' ≪≫ e2⟩

private theorem _root_.Compat1.generic
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR cX ε k
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    {C₁ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (i₁ : SchemeHomOver c₁ (baseChange R cX k))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ specMap R k = specMap R k)
    (F : pullback cX (specMap R k) ⟶ pullback cX (specMap R k))
    (hF₁ : F ≫ pullback.fst cX (specMap R k) = pullback.fst cX (specMap R k))
    (hF₂ : F ≫ pullback.snd cX (specMap R k) = pullback.snd cX (specMap R k) ≫ φ)
    (Fk : pullback (baseChange R cX k) (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback (baseChange R cX k) (𝟙 (Spec (CommRingCat.of k))))
    (hFk₁ : Fk ≫ pullback.fst (baseChange R cX k) (𝟙 _) = pullback.fst (baseChange R cX k) (𝟙 _) ≫ F)
    (hFk₂ : Fk ≫ pullback.snd (baseChange R cX k) (𝟙 _) = pullback.snd (baseChange R cX k) (𝟙 _) ≫ φ)
    (F₁ : C₁ ⟶ C₁) (hF₁i : F₁ ≫ i₁.1 = i₁.1 ≫ F)
    (F₁k : pullback c₁ (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback c₁ (𝟙 (Spec (CommRingCat.of k))))
    (hF₁k₁ : F₁k ≫ pullback.fst c₁ (𝟙 _) = pullback.fst c₁ (𝟙 _) ≫ F₁)
    (hF₁k₂ : F₁k ≫ pullback.snd c₁ (𝟙 _) = pullback.snd c₁ (𝟙 _) ≫ φ)
    (v v' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hv : v'.1 ≫ pullback.fst D.toBase (specMap R k) = φ ≫ v.1 ≫ pullback.fst D.toBase (specMap R k)) :
    Nonempty ((hrep₁.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) v')).L ≅
      (Scheme.Modules.pullback F₁k).obj
        (hrep₁.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) v)).L) := by
  obtain ⟨rv⟩ := restrict cX ε D k hreps c₁ i₁ ε₁ hε₁ D₁ hrep₁ v
  obtain ⟨rv'⟩ := restrict cX ε D k hreps c₁ i₁ ε₁ hε₁ D₁ hrep₁ v'
  obtain ⟨tw⟩ := TwistBC.generic cX ε D hrep k hreps hPk φ hφ F hF₁ hF₂ Fk hFk₁ hFk₂ v v' hv

  have hkey : F₁k ≫ curveChange i₁.1 i₁.2 (𝟙 _) = curveChange i₁.1 i₁.2 (𝟙 _) ≫ Fk := by
    apply pullback.hom_ext
    · have h1 : curveChange i₁.1 i₁.2 (𝟙 (Spec (CommRingCat.of k))) ≫ pullback.fst (baseChange R cX k) (𝟙 _) =
          pullback.fst c₁ (𝟙 _) ≫ i₁.1 := by
        simp only [curveChange, pullback.lift_fst]
      rw [Category.assoc, h1, ← Category.assoc, hF₁k₁, Category.assoc, hF₁i, Category.assoc, hFk₁, ← Category.assoc,
        ← Category.assoc, h1]
    · rw [Category.assoc, curveChange_snd, hF₁k₂, Category.assoc, hFk₂, ← Category.assoc, curveChange_snd]
  exact ⟨rv' ≪≫ (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).mapIso tw ≪≫
    (Scheme.Modules.pullbackComp (curveChange i₁.1 i₁.2 (𝟙 _)) Fk).app _ ≪≫
    (Scheme.Modules.pullbackCongr hkey.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp F₁k (curveChange i₁.1 i₁.2 (𝟙 _))).app _).symm ≪≫
    (Scheme.Modules.pullback F₁k).mapIso rv.symm⟩

p2m_export "Compat1" "generic"
end Compat1

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))

    (hφ : Spec.map (CommRingCat.ofHom (frobenius k p)) ≫ specMap A k = specMap A k)

    (F : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hF₁ : F ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hF₂ : F ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ Spec.map (CommRingCat.ofHom (frobenius k p)))
    (Fk : pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 (Spec (CommRingCat.of k))))
    (hFk₁ : Fk ≫ pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 (Spec (CommRingCat.of k))) = pullback.fst (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 (Spec (CommRingCat.of k))) ≫ F)
    (hFk₂ : Fk ≫ pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 (Spec (CommRingCat.of k))) = pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (frobenius k p)))

    (F₁ : C₁ ⟶ C₁) (hF₁i : F₁ ≫ i₁.1 = i₁.1 ≫ F)
    (F₁k : pullback c₁ (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback c₁ (𝟙 (Spec (CommRingCat.of k))))
    (hF₁k₁ : F₁k ≫ pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) = pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ F₁)
    (hF₁k₂ : F₁k ≫ pullback.snd c₁ (𝟙 (Spec (CommRingCat.of k))) = pullback.snd c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (frobenius k p)))

    (v v' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hv : v'.1 ≫ pullback.fst D.toBase (specMap A k) =
      Spec.map (CommRingCat.ofHom (frobenius k p)) ≫ v.1 ≫ pullback.fst D.toBase (specMap A k)) :
    Nonempty ((hrep₁.some.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) v')).L ≅
      (Scheme.Modules.pullback F₁k).obj
        (hrep₁.some.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) v)).L) :=
  Compat1.generic (ModularCurve.TwoChart.modelTo A (↥K) j) ε D hrep.some k hreps hPk c₁ i₁ ε₁ hε₁ D₁ hrep₁.some
    (Spec.map (CommRingCat.ofHom (frobenius k p))) hφ F hF₁ hF₂ Fk hFk₁ hFk₂ F₁ hF₁i F₁k hF₁k₁ hF₁k₂ v v' hv

end S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_obj_of_comp_fst_eq_frobenius_comp_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_obj_of_comp_fst_eq_frobenius_comp_twoChartModel_x1_mul (solution)
