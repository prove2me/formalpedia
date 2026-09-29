-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_frobHom_classifies_normModule_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/46d89089-1c8a-528a-9cba-73ce10c7c419

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

import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd_curveChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel"

noncomputable section

namespace FrobHomAux

universe u

section CurveChange

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (π : C' ⟶ C) (hπ : π ≫ c = c')

theorem isFinite_curveChange [IsFinite π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite π› (inferInstance : IsFinite (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem flat_curveChange [Flat π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Flat (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @Flat) ‹Flat π› (inferInstance : Flat (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation π] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : LocallyOfFinitePresentation (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) ‹LocallyOfFinitePresentation π›
    (inferInstance : LocallyOfFinitePresentation (𝟙 T)) hπ.symm (Category.id_comp t).symm

theorem finrank_curveChange [Flat π] [IsFinite π] {d : ℕ} (hd : ∀ y : C, π.finrank y = d)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∀ y, (curveChange π hπ t).finrank y = d :=
  fun y => (Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t π hπ y).trans (hd _)

end CurveChange

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (π : C' ⟶ C) (hπ : π ≫ c = c')
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (d : ℕ) (hd : ∀ y : C, π.finrank y = d)

include hd

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange π hπ t) d M.L) :=
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  Scheme.Modules.IsInvertible.normModule _ d (finrank_curveChange π hπ hd t) M.isInvertible

def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    RigidifiedLineBundle c ε t :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    (Scheme.Modules.normModule (curveChange π hπ t) d M.L) (hinv π hπ d hd t M)

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    (Phi (ε := ε) π hπ d hd t M).L =
      (RigidifiedLineBundle.ofInvertible (ε := ε)
        (Scheme.Modules.normModule (curveChange π hπ t) d M.L) (hinv π hπ d hd t M)).L := rfl

theorem hcongr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t)
    (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi (ε := ε) π hπ d hd t M).L ≅ (Phi (ε := ε) π hπ d hd t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.normModuleMapIso _ d h.some)

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε := ε) π hπ d hd t M) :=
  FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange (ε := ε) π hπ d hd M.L M.isInvertible
    (fun k _ _ s => hM k s) (hinv π hπ d hd t M)

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε := ε) π hπ d hd t (RigidifiedLineBundle.unit (c := c') (ε := ε') t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨eN⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t)
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv π hπ d hd t (RigidifiedLineBundle.unit t))
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t).isInvertible eN
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t)
  exact ⟨e1 ≪≫ e2⟩

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t) :
    Nonempty ((Phi (ε := ε) π hπ d hd t (M.tensor M')).L ≅
      ((Phi (ε := ε) π hπ d hd t M).tensor (Phi (ε := ε) π hπ d hd t M')).L) := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨eT⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t) _ _ M.isInvertible M'.isInvertible
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv π hπ d hd t (M.tensor M')) ((hinv π hπ d hd t M).tensor (hinv π hπ d hd t M')) eT
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε)
    (hinv π hπ d hd t M) (hinv π hπ d hd t M')
  exact ⟨e1 ≪≫ e2⟩

theorem hnat {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t) :
    Nonempty (((Phi (ε := ε) π hπ d hd t M).pullbackAlong ψ).L ≅
      (Phi (ε := ε) π hπ d hd t' (M.pullbackAlong ψ)).L) := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t

  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) ψ
    (hinv π hπ d hd t M)

  obtain ⟨e2⟩ := Scheme.Modules.nonempty_pullback_normModule_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t) (baseChangeSnd c ψ) (curveChange π hπ t') (baseChangeSnd c' ψ)
    (isPullback_baseChangeSnd_curveChange π hπ ψ) M.isInvertible
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((hinv π hπ d hd t M).pullback (baseChangeSnd c ψ)) (hinv π hπ d hd t' (M.pullbackAlong ψ)) e2
  exact ⟨e1 ≪≫ e3⟩

end Transform

end FrobHomAux

end

open FrobHomAux in
set_option maxHeartbeats 3200000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p) :
    ∃ F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase,

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
            (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L))) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (x y : SchemeHomOver t (D₀.baseChange κ).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul t x y) F =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul t
            (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) ∧

      (D₀.baseChange κ).zeroSection ≫ F.1 = (D₀.baseChange κ).zeroSection := by

  obtain ⟨N0, hN0, -⟩ := RepresentsRelSubPic.existsUnique_hom_of_transform hD₀κ hD₀κ
    (Phi (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk)
    (fun t M M' e => hcongr (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t M M' e)
    (fun ψ M => hnat (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk ψ M)
    (fun t M hM => hcut (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t M hM)
  have hhom := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀))
    (P' := algEquivZeroGroupCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) hD₀κ hD₀κ
    (Phi (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk)
    (fun t M hM => hcut (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t M hM)
    (fun t M M' => htensor (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t M M')
    (fun t => hunit (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t) N0 hN0

  have pin : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b N0)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)) := by
    intro T t b
    let M : RigidifiedLineBundle (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀) t :=
      hD₀κ.poincare.pullbackAlong b
    have hM : (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)).P t M :=
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)).pullback_mem _ _ b _ hD₀κ.poincare_mem
    have hb : b = hD₀κ.classify t M hM := hD₀κ.classify_unique _ M hM b ⟨Iso.refl _⟩
    have hNb : postComp N0 b = hD₀κ.classify t (Phi (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t M)
        (hcut (ε := sectionBaseChange κ ε₀) φκ hφκ_over p hφ_rk t M hM) := by
      conv_lhs => rw [hb]
      exact hN0 t M hM
    have e : NeronModelInfra.schemeHomOverComp b N0 = postComp N0 b := rfl
    rw [e, hNb]
    exact hD₀κ.classify_spec _ _ _
  exact ⟨N0, fun t b => pin t b, fun t x y => hhom.1 t x y, hhom.2⟩

end S_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange (solution)
