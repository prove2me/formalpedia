-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/327879ba-a90c-5a34-90ec-9c4ec36b741b

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

namespace AOPKit

universe u

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

open _root_.AlgebraicGeometry.Scheme.IdealSheafData in
theorem isInvertible_prod {Y : Scheme.{u}} {ι : Type*} (s : Finset ι) (J : ι → Y.IdealSheafData)
    (hJ : ∀ i ∈ s, (J i).IsInvertible) : (∏ i ∈ s, J i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isInvertible_top : (⊤ : Y.IdealSheafData).IsInvertible)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hJ a (Finset.mem_insert_self a s)).mul (ih fun i hi => hJ i (Finset.mem_insert_of_mem hi))

def ttComm {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (W X Y Z : C) :
    (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ W X (Y ⊗ Z) ≪≫ whiskerLeftIso W ((α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z) ≪≫ (α_ W Y (X ⊗ Z)).symm

end AOPKit

open AOPKit _root_.AlgebraicGeometry.Scheme.IdealSheafData in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
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
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (s : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))))
    (m : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → ℕ)
    (ybar : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → SchemeHomOver (genPt p) (toBase N₀ p))
    (hybar : ∀ w, (ybar w).1 = (𝔓.Meta.pointEquivPlace.symm w).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      ∑ w ∈ s, (m w : ℤ) • Finsupp.single w 1 -
        ((∑ w ∈ s, m w : ℕ) : ℤ) • Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1) :
        Nonempty ((hD.poincare.pullbackAlong (pts (Pic0.mk Dv))).L ≅
      (∏ w ∈ s, (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ m w).invModule ⊗
        ((RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1)
            ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _)))).I ^
          (∑ w ∈ s, m w)).module) := by
  classical

  let X := pullback (toBase N₀ p) (genPt p)
  have hε : (genPt p ≫ 𝔓.εinf.1) ≫ toBase N₀ p = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _))
  let I : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → X.IdealSheafData :=
    fun w => (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I
  let Iε : X.IdealSheafData := (RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1) hε).I

  let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
  letI grp : Group (SchemeHomOver (genPt p) D.toBase) := L.pointGroup _
  have hcomm : L.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut _ _) hD
  letI cgrp : CommGroup (SchemeHomOver (genPt p) D.toBase) := { grp with mul_comm := fun a b => hcomm (genPt p) a b }
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hD

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    first | rfl | (congr 2; exact IsScalarTower.algebraMap_eq _ _ _)
  have hΦinv : (pullback.fst (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
      pullback.fst (toBase N₀ p) (specMap (R p) ℚ)) ≫ toBase N₀ p =
      pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫ genPt p := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback (toBase N₀ p) (genPt p) ≅ pullback (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kQ (pullback.snd (toBase N₀ p) (genPt p)) hkQ₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ)) (pullback.snd _ _) hΦinv
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hkQ₁, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, hkQ₁, pullback.lift_fst]
          · rw [Category.assoc, hkQ₂, pullback.lift_snd_assoc]
            exact (pullback.condition).symm
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd (toBase N₀ p) (genPt p) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI := 𝔓.smooth_generic
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance
  haveI hsX : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) (genPt p)) :=
    AOPKit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd (toBase N₀ p) (genPt p)) := inferInstance

  have hI : ∀ w, (I w).IsInvertible := fun w =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase N₀ p) (genPt p))
      (graphOver (toBase N₀ p) (ybar w).1 (ybar w).2) (graphOver_snd _ _ _)
  have hIε : Iε.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase N₀ p) (genPt p))
      (graphOver (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1) hε) (graphOver_snd _ _ _)

  have hAJ : ∀ w, ∃ dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
      (dw : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
        Finsupp.single w 1 - Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1 ∧
      (pts (Pic0.mk dw)).1 = (𝔓.Meta.pointEquivPlace.symm w).1 ≫ ajbar := by
    intro w
    obtain ⟨dw, h1, h2⟩ := hpts_aj (𝔓.Meta.pointEquivPlace.symm w) εbar hεbar
    exact ⟨dw, by rw [h1, Equiv.apply_symm_apply], h2⟩
  choose d hd₁ hd₂ using hAJ

  have hP1 : ∀ w, Nonempty ((hD.poincare.pullbackAlong (pts (Pic0.mk (d w)))).L ≅ (I w).invModule ⊗ Iε.module) := by
    intro w
    exact ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
      N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ ajbar hajbar (𝔓.Meta.pointEquivPlace.symm w) (ybar w) (hybar w)
      (pts (Pic0.mk (d w))) (hd₂ w)

  have hPmul : ∀ a b : SchemeHomOver (genPt p) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong (a * b)).L ≅ (hD.poincare.pullbackAlong a).L ⊗ (hD.poincare.pullbackAlong b).L) := by
    intro a b
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD
      (T := Over.mk (genPt p)) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
    exact this
  have hPone : Nonempty ((hD.poincare.pullbackAlong (1 : SchemeHomOver (genPt p) D.toBase)).L ≅ 𝟙_ X.Modules) := by
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := algEquivZeroGroupCut _ _) hD (Over.mk (genPt p))
    exact this

  have pts_mul : ∀ x y : JZero (N₀ * p), pts (x + y) = pts x * pts y := fun x y => hpts_add x y
  have pts_zero : pts 0 = 1 := by
    have h : pts 0 * pts 0 = pts 0 * 1 := by rw [mul_one, ← pts_mul, add_zero]
    exact mul_left_cancel h
  have pts_nsmul : ∀ (n : ℕ) (x : JZero (N₀ * p)), pts (n • x) = pts x ^ n := by
    intro n x
    induction n with
    | zero => rw [zero_nsmul, pow_zero, pts_zero]
    | succ n ih => rw [succ_nsmul, pts_mul, ih, pow_succ]

  have hPpow : ∀ (a : SchemeHomOver (genPt p) D.toBase) (M : X.Modules), Nonempty ((hD.poincare.pullbackAlong a).L ≅ M) →
      ∀ n : ℕ, ∀ (J : X.IdealSheafData), J.IsInvertible → ∀ (E : X.IdealSheafData), E.IsInvertible →
      Nonempty (M ≅ J.invModule ⊗ E.module) →
      Nonempty ((hD.poincare.pullbackAlong (a ^ n)).L ≅ (J ^ n).invModule ⊗ (E ^ n).module) := by
    intro a M hM n J hJ E hE hMJE
    obtain ⟨eM⟩ := hM
    obtain ⟨eJE⟩ := hMJE
    induction n with
    | zero =>
      obtain ⟨e1⟩ := hPone
      obtain ⟨-, ⟨eT⟩⟩ := (isInvertible_top : (⊤ : X.IdealSheafData).IsInvertible).nonempty_module_tensor_invModule_iso
      refine ⟨?_⟩
      rw [pow_zero, pow_zero, pow_zero]
      exact e1 ≪≫ eT.symm
    | succ n ih =>
      obtain ⟨en⟩ := ih
      obtain ⟨em⟩ := hPmul (a ^ n) a
      obtain ⟨eJ⟩ := (hJ.pow n).nonempty_mul_invModule_iso_tensor hJ
      obtain ⟨eE⟩ := (hE.pow n).nonempty_mul_module_iso_tensor hE
      refine ⟨?_⟩
      rw [pow_succ, pow_succ, pow_succ]
      exact em ≪≫ (en ⊗ᵢ (eM ≪≫ eJE)) ≪≫ AOPKit.ttComm _ _ _ _ ≪≫ (eJ.symm ⊗ᵢ eE.symm)

  have hDv' : Dv = ∑ w ∈ s, m w • d w := by
    apply Subtype.ext
    rw [hDv]
    simp only [AddSubmonoidClass.coe_finset_sum, AddSubmonoidClass.coe_nsmul, hd₁, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul]
    simp only [← natCast_zsmul, Nat.cast_sum]
  have hmk : ∀ (t : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))),
      Pic0.mk (∑ w ∈ t, m w • d w) = ∑ w ∈ t, m w • Pic0.mk (d w) := by
    intro t
    show (QuotientAddGroup.mk' _) (∑ w ∈ t, m w • d w) = ∑ w ∈ t, m w • (QuotientAddGroup.mk' _) (d w)
    rw [map_sum]
    simp only [map_nsmul]
  have hpts : pts (Pic0.mk Dv) = ∏ w ∈ s, pts (Pic0.mk (d w)) ^ m w := by
    rw [hDv', hmk]

    have key : ∀ (t : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))),
        pts (∑ w ∈ t, m w • Pic0.mk (d w)) = ∏ w ∈ t, pts (Pic0.mk (d w)) ^ m w := by
      intro t
      induction t using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.prod_empty, pts_zero]
      | insert w t hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, pts_mul, ih, pts_nsmul]
    exact key s

  have main : ∀ (t : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))),
      Nonempty ((hD.poincare.pullbackAlong (∏ w ∈ t, pts (Pic0.mk (d w)) ^ m w)).L ≅
        (∏ w ∈ t, I w ^ m w).invModule ⊗ (Iε ^ (∑ w ∈ t, m w)).module) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      obtain ⟨e1⟩ := hPone
      obtain ⟨-, ⟨eT⟩⟩ := (isInvertible_top : (⊤ : X.IdealSheafData).IsInvertible).nonempty_module_tensor_invModule_iso
      refine ⟨?_⟩
      rw [Finset.prod_empty, Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact e1 ≪≫ eT.symm
    | insert w t hw ih =>
      obtain ⟨et⟩ := ih
      obtain ⟨ew⟩ := hPpow (pts (Pic0.mk (d w))) _ (hP1 w) (m w) (I w) (hI w) Iε hIε ⟨Iso.refl _⟩
      obtain ⟨em⟩ := hPmul (pts (Pic0.mk (d w)) ^ m w) (∏ x ∈ t, pts (Pic0.mk (d x)) ^ m x)
      have hJt : (∏ x ∈ t, I x ^ m x).IsInvertible := isInvertible_prod t _ fun x _ => (hI x).pow _
      obtain ⟨eJ⟩ := ((hI w).pow (m w)).nonempty_mul_invModule_iso_tensor hJt
      obtain ⟨eE⟩ := (hIε.pow (m w)).nonempty_mul_module_iso_tensor (hIε.pow (∑ x ∈ t, m x))
      refine ⟨?_⟩
      rw [Finset.prod_insert hw, Finset.prod_insert hw, Finset.sum_insert hw, pow_add]
      exact em ≪≫ (ew ⊗ᵢ et) ≪≫ AOPKit.ttComm _ _ _ _ ≪≫ (eJ.symm ⊗ᵢ eE.symm)
  rw [hpts]
  exact main s

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow (solution)
