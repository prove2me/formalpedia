-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/046ddae0-6c91-52ea-a14a-9c900dd52e54

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

namespace L5bKitC
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

noncomputable def monoidalCancel {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    (eN : N ⊗ N' ≅ 𝟙_ C) (e : M ⊗ N ≅ M' ⊗ N) : M ≅ M' :=
  (ρ_ M).symm ≪≫ (whiskerLeftIso M eN.symm) ≪≫ (α_ M N N').symm ≪≫ (whiskerRightIso e N') ≪≫ α_ M' N N' ≪≫
    whiskerLeftIso M' eN ≪≫ ρ_ M'
end L5bKitC

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

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

    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₁ : Spec.map (CommRingCat.ofHom A.subtype) ≫ u₁.1 =
      y₁.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (hu₁sm : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu₂ : Spec.map (CommRingCat.ofHom A.subtype) ≫ u₂.1 =
      y₂.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (hu₂sm : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))

    (Dv : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)

    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (ha : Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule)) :
    (pts (Pic0.mk Dv)).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ a.1 := by
  obtain ⟨eS⟩ := ha
  haveI : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := inferInstance

  have hbar : barPt A ≫ Spec.map (CommRingCat.ofHom ρ) = genPt p := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  let g' : SchemeHomOver (genPt p) D.toBase := ⟨barPt A ≫ a.1, by rw [Category.assoc, a.2, hbar]⟩
  suffices h : pts (Pic0.mk Dv) = g' from congrArg (fun g : SchemeHomOver (genPt p) D.toBase => g.1) h
  refine hD.ext_of_iso (genPt p) (pts (Pic0.mk Dv)) g' ?_

  obtain ⟨D₁, hD₁, hD₁pts⟩ := hpts_aj y₁ εbar hεbar
  obtain ⟨D₂, hD₂, hD₂pts⟩ := hpts_aj y₂ εbar hεbar
  have hDv12 : Dv = D₁ - D₂ := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, hDv, hD₁, hD₂]
    abel

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
  letI grp : Group (SchemeHomOver (genPt p) D.toBase) := Lw.pointGroup _
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hD
  have pts_mul : ∀ x y : JH M H, pts (x + y) = pts x * pts y := fun x y => hpts_add x y
  have hkey : pts (Pic0.mk Dv) * pts (Pic0.mk D₂) = pts (Pic0.mk D₁) := by
    rw [← pts_mul]
    congr 1
    show (QuotientAddGroup.mk' _) Dv + (QuotientAddGroup.mk' _) D₂ = (QuotientAddGroup.mk' _) D₁
    rw [← map_add, hDv12, sub_add_cancel]

  have hy₁c : (barPt A ≫ u₁.1) ≫ toBase p (ΓM M H) hj = genPt p := by rw [Category.assoc, u₁.2, hbar]
  have hy₂c : (barPt A ≫ u₂.1) ≫ toBase p (ΓM M H) hj = genPt p := by rw [Category.assoc, u₂.2, hbar]
  obtain ⟨eP₁⟩ := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajQ hkQ₁ hkQ₂ hajbar y₁ ⟨barPt A ≫ u₁.1, hy₁c⟩ hu₁ (pts (Pic0.mk D₁)) hD₁pts
  obtain ⟨eP₂⟩ := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajQ hkQ₁ hkQ₂ hajbar y₂ ⟨barPt A ≫ u₂.1, hy₂c⟩ hu₂ (pts (Pic0.mk D₂)) hD₂pts
  have hPmul : ∀ a b : SchemeHomOver (genPt p) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong (a * b)).L ≅ (hD.poincare.pullbackAlong a).L ⊗ (hD.poincare.pullbackAlong b).L) := by
    intro a b
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD
      (T := Over.mk (genPt p)) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
    exact this
  have hPone : Nonempty ((hD.poincare.pullbackAlong (1 : SchemeHomOver (genPt p) D.toBase)).L ≅
      𝟙_ (pullback (toBase p (ΓM M H) hj) (genPt p)).Modules) := by
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := algEquivZeroGroupCut _ _) hD (Over.mk (genPt p))
    exact this

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    first | rfl | (congr 2; exact IsScalarTower.algebraMap_eq _ _ _)
  have hΦinv : (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
      pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ)) ≫ toBase p (ΓM M H) hj =
      pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫ genPt p := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback (toBase p (ΓM M H) hj) (genPt p) ≅
      pullback (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kQ (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) hkQ₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ)) (pullback.snd _ _) hΦinv
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
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd (toBase p (ΓM M H) hj) (genPt p) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI := 𝔛.smooth_generic
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance
  haveI hsX : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) :=
    L5bKitC.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) := inferInstance

  have hI₂ := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p (ΓM M H) hj) (genPt p))
    (graphOver (toBase p (ΓM M H) hj) (barPt A ≫ u₂.1) hy₂c) (graphOver_snd _ _ _)
  obtain ⟨⟨eI₂⟩, -⟩ := hI₂.nonempty_module_tensor_invModule_iso

  obtain ⟨em⟩ := hPmul (pts (Pic0.mk Dv)) (pts (Pic0.mk D₂))
  have hba : hD.poincare.pullbackAlong (pts (Pic0.mk Dv) * pts (Pic0.mk D₂)) = hD.poincare.pullbackAlong (pts (Pic0.mk D₁)) := by
    rw [hkey]
  have eL : (hD.poincare.pullbackAlong (pts (Pic0.mk Dv))).L ⊗ (hD.poincare.pullbackAlong (pts (Pic0.mk D₂))).L ≅
      (hD.poincare.pullbackAlong (pts (Pic0.mk D₁))).L := em.symm ≪≫ eqToIso (congrArg (fun M => M.L) hba)
  obtain ⟨em2⟩ := hPmul (pts (Pic0.mk D₂)) (pts (Pic0.mk D₂))⁻¹
  obtain ⟨e1⟩ := hPone
  have hone : hD.poincare.pullbackAlong (pts (Pic0.mk D₂) * (pts (Pic0.mk D₂))⁻¹) = hD.poincare.pullbackAlong 1 := by
    rw [mul_inv_cancel]
  have eN : (hD.poincare.pullbackAlong (pts (Pic0.mk D₂))).L ⊗ (hD.poincare.pullbackAlong (pts (Pic0.mk D₂))⁻¹).L ≅
      𝟙_ (pullback (toBase p (ΓM M H) hj) (genPt p)).Modules := em2.symm ≪≫ eqToIso (congrArg (fun M => M.L) hone) ≪≫ e1

  let L₁ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (barPt A ≫ u₁.1) hy₁c).lineBundle
  let L₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (barPt A ≫ u₂.1) hy₂c).lineBundle
  let J₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (barPt A ≫ u₂.1) hy₂c).idealModule
  let Jε := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1)
    ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _)))).idealModule
  have e' : (L₁ ⊗ J₂) ⊗ (hD.poincare.pullbackAlong (pts (Pic0.mk D₂))).L ≅ (hD.poincare.pullbackAlong (pts (Pic0.mk D₁))).L :=
    whiskerLeftIso (L₁ ⊗ J₂) eP₂ ≪≫ α_ L₁ J₂ (L₂ ⊗ Jε) ≪≫ whiskerLeftIso L₁ ((α_ J₂ L₂ Jε).symm ≪≫ whiskerRightIso eI₂ Jε ≪≫ λ_ Jε) ≪≫
      eP₁.symm
  have eLM : (hD.poincare.pullbackAlong (pts (Pic0.mk Dv))).L ≅ L₁ ⊗ J₂ := L5bKitC.monoidalCancel eN (eL ≪≫ e'.symm)

  have eR : Nonempty ((hD.poincare.pullbackAlong g').L ≅ L₁ ⊗ J₂) := by
    let ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ)) := ⟨barPt A, hbar⟩
    have hcomp : baseChangeSnd (toBase p (ΓM M H) hj) g' =
        baseChangeSnd (toBase p (ΓM M H) hj) ψ ≫ baseChangeSnd (toBase p (ΓM M H) hj) a := by
      apply pullback.hom_ext
      · rw [Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst']
      · rw [Category.assoc, BaseChange.baseChangeSnd_snd', BaseChange.baseChangeSnd_snd']
        simp only [← Category.assoc]
        rw [BaseChange.baseChangeSnd_snd']
        exact (Category.assoc _ _ _).symm
    haveI := 𝔛.smoothLocus_relDim
    obtain ⟨⟨e₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) (toBase p (ΓM M H) hj) 𝔛.smoothLocus u₁ hu₁sm ψ hy₁c
    obtain ⟨-, ⟨e₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) (toBase p (ΓM M H) hj) 𝔛.smoothLocus u₂ hu₂sm ψ hy₂c
    exact ⟨(Scheme.Modules.pullbackCongr hcomp).app hD.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓM M H) hj) ψ)).mapIso eS ≪≫
      Scheme.Modules.pullbackTensorObjIso (baseChangeSnd (toBase p (ΓM M H) hj) ψ) _ _ ≪≫ (e₁ ⊗ᵢ e₂)⟩
  obtain ⟨eR⟩ := eR
  exact ⟨eLM ≪≫ eR.symm⟩

end S_ModularCurve_XHDRModelAtP_pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_pts_pic0Mk_eq_barPt_comp_of_poincare_pullbackAlong_iso_ofPoint_tensor_idealModule (solution)
