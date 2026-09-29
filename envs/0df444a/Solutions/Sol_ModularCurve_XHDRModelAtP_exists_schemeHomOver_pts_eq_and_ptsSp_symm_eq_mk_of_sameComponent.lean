-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/056b4c17-a2dd-563a-9b4f-72afbb1a5a22

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

namespace L5bKit
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
end L5bKit

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P)
    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hpts_law : ∀ x y : JH M H,
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
        SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hPTSDIV : ∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x) :
    (∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        (pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x) := by
  intro i y₁ u₁ hu₁y hu₁sm uκ₁ huκ₁f huκ₁s P₁ hP₁ y₂ u₂ hu₂y hu₂sm uκ₂ huκ₂f huκ₂s P₂ hP₂ Dv hDv x hx0 hx1 hx2

  obtain ⟨s, ⟨eS⟩, hsp⟩ := hPTSDIV i u₁ hu₁sm uκ₁ huκ₁f huκ₁s P₁ hP₁ u₂ hu₂sm uκ₂ huκ₂f huκ₂s P₂ hP₂ x hx0 hx1 hx2
  refine ⟨s, ?_, hsp⟩

  have hbar : barPt A ≫ Spec.map (CommRingCat.ofHom ρ) = genPt p := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  let g' : SchemeHomOver (genPt p) D.toBase := ⟨barPt A ≫ s.1, by rw [Category.assoc, s.2, hbar]⟩
  suffices h : pts (Pic0.mk Dv) = g' from congrArg (fun g : SchemeHomOver (genPt p) D.toBase => g.1) h
  refine hD.ext_of_iso (genPt p) (pts (Pic0.mk Dv)) g' ?_

  haveI : IsIso 𝔛.eeta := 𝔛.eeta_iso
  have hεc : (genPt p ≫ 𝔛.εinf.1) ≫ toBase p (ΓM M H) hj = 𝟙 _ ≫ genPt p := by
    rw [Category.assoc, 𝔛.εinf.2, Category.comp_id, Category.id_comp]
  let εpt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback (toBase p (ΓM M H) hj) (genPt p) :=
    pullback.lift (genPt p ≫ 𝔛.εinf.1) (𝟙 _) hεc
  have hinv : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, 𝔛.heeta]
  let εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
    ⟨εpt ≫ inv 𝔛.eeta, by rw [Category.assoc, hinv, pullback.lift_snd]⟩
  have hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 := by
    show (εpt ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  obtain ⟨D₁, hD₁, hD₁pts⟩ := hAJ y₁ εbar hεbar
  obtain ⟨D₂, hD₂, hD₂pts⟩ := hAJ y₂ εbar hεbar
  have hDv12 : Dv = D₁ - D₂ := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, hDv, hD₁, hD₂]
    abel

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
  letI grp : Group (SchemeHomOver (genPt p) D.toBase) := Lw.pointGroup _
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hD
  have pts_mul : ∀ x y : JH M H, pts (x + y) = pts x * pts y := fun x y => hpts_law x y
  have hkey : pts (Pic0.mk Dv) * pts (Pic0.mk D₂) = pts (Pic0.mk D₁) := by
    rw [← pts_mul]
    congr 1
    show (QuotientAddGroup.mk' _) Dv + (QuotientAddGroup.mk' _) D₂ = (QuotientAddGroup.mk' _) D₁
    rw [← map_add, hDv12, sub_add_cancel]

  have hy₁c : (barPt A ≫ u₁.1) ≫ toBase p (ΓM M H) hj = genPt p := by rw [Category.assoc, u₁.2, hbar]
  have hy₂c : (barPt A ≫ u₂.1) ≫ toBase p (ΓM M H) hj = genPt p := by rw [Category.assoc, u₂.2, hbar]
  obtain ⟨eP₁⟩ := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajcl hkQ₁ hkQ₂ hajbar y₁ ⟨barPt A ≫ u₁.1, hy₁c⟩ hu₁y (pts (Pic0.mk D₁)) hD₁pts
  obtain ⟨eP₂⟩ := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    p M H hpM hj 𝔛 D hD hDQ ajQ kQ ajbar hPQ hajcl hkQ₁ hkQ₂ hajbar y₂ ⟨barPt A ≫ u₂.1, hy₂c⟩ hu₂y (pts (Pic0.mk D₂)) hD₂pts
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
    L5bKit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
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
  have eLM : (hD.poincare.pullbackAlong (pts (Pic0.mk Dv))).L ≅ L₁ ⊗ J₂ := L5bKit.monoidalCancel eN (eL ≪≫ e'.symm)

  have eR : Nonempty ((hD.poincare.pullbackAlong g').L ≅ L₁ ⊗ J₂) := by
    let ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ)) := ⟨barPt A, hbar⟩
    have hcomp : baseChangeSnd (toBase p (ΓM M H) hj) g' =
        baseChangeSnd (toBase p (ΓM M H) hj) ψ ≫ baseChangeSnd (toBase p (ΓM M H) hj) s := by
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

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent (solution)
