-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_representsRelSubPic_torus_abq_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/56cfcc9a-0c68-5dc1-8ac2-84d2083b904a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_SupersingularNodePlaces

import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_flat_surjective_restrictPair_of_twoGluedSmoothCurves
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_torus_abq_specialFibre
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.SplitTorus ModularCurve ModularCurve.DRLevel

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    [IsProper (baseChange (R p) (toBase N₀ p) κ)]
    [IsProper (baseChange (R p) (toBase0 N₀ p) κ)] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) κ)]
    [GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) κ)]

    (ε₀κ : Spec (CommRingCat.of κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hε₀κ₁ : ε₀κ ≫ pullback.fst _ _ = specMap (R p) κ ≫ ε₀.1) (hε₀κ₂ : ε₀κ ≫ pullback.snd _ _ = 𝟙 _)
    (hε₁ : ε₀κ ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = sectionFibre 𝔓.εinf (algebraMap (R p) κ)) :

    Nat.card ↥(pullback (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1)) =
        Nat.card ↥(ssPlaces p N₀ κ) ∧
    0 < Nat.card ↥(ssPlaces p N₀ κ) ∧

    ∃ (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)) (D.baseChange κ))
      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf κ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ κ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange κ ε₀).1 ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = (sectionBaseChange κ 𝔓.εinf).1)
      (τ : SchemeHomOver (torusStr κ (Nat.card ↥(ssPlaces p N₀ κ) - 1)) (D.baseChange κ).toBase)
      (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase),

      abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0)
        hε₁' hDκ hD₀κ ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
            ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1)
              (𝔓.comp_over κ (algebraMap (R p) κ) 1) t)).obj (hDκ.poincare.pullbackAlong a).L))) ∧

      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) →ₐ[κ] κ),
        NeronModelInfra.schemeHomOverComp (torusPtId κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) (χ * χ').ofConv) τ =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (R p) κ)).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) χ'.ofConv) τ)) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t (D.baseChange κ).toBase),
        NeronModelInfra.schemeHomOverComp
            (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (R p) κ)).mul t a b)
            (abq i) =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) κ)).mul t
            (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i))) ∧

      Flat (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
        (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) κ)).one t) ↔
          ∃ y : SchemeHomOver t (torusStr κ (Nat.card ↥(ssPlaces p N₀ κ) - 1)),
            NeronModelInfra.schemeHomOverComp y τ = a) := by
  classical
  haveI hci₀ : IsClosedImmersion (𝔓.comp κ (algebraMap (R p) κ) 0) := 𝔓.comp_isClosedImmersion κ _ 0
  haveI hci₁ : IsClosedImmersion (𝔓.comp κ (algebraMap (R p) κ) 1) := 𝔓.comp_isClosedImmersion κ _ 1

  obtain ⟨hDκ, hP⟩ := exists_representsRelSubPic_baseChange (R p) (toBase N₀ p) 𝔓.εinf D hD κ
  obtain ⟨hD₀κ, hP₀⟩ := exists_representsRelSubPic_baseChange (R p) (toBase0 N₀ p) ε₀ D₀ hD₀ κ
  have Lκ := relativeGroupLaw_baseChange_eq (R p) (toBase N₀ p) 𝔓.εinf D hD κ hDκ hP
  have L₀κ := relativeGroupLaw_baseChange_eq (R p) (toBase0 N₀ p) ε₀ D₀ hD₀ κ hD₀κ hP₀

  have hε₀κ : ε₀κ = (sectionBaseChange κ ε₀).1 := by
    apply pullback.hom_ext
    · rw [hε₀κ₁]; exact (pullback.lift_fst _ _ _).symm
    · rw [hε₀κ₂]; exact (pullback.lift_snd _ _ _).symm
  have hε₁' : (sectionBaseChange κ ε₀).1 ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = (sectionBaseChange κ 𝔓.εinf).1 := by
    rw [← hε₀κ, hε₁]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hXred : IsReduced (pullback (toBase N₀ p) (specMap (R p) κ)) := 𝔓.fibre_reduced κ (algebraMap (R p) κ)
  have hcard : Nat.card ↥(pullback (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1)) =
      Nat.card ↥(ssPlaces p N₀ κ) := Nat.card_congr (𝔓.nodeEquiv κ (algebraMap (R p) κ))
  have hs0 : 0 < Nat.card ↥(ssPlaces p N₀ κ) := by
    haveI : Finite ↥(ssPlaces p N₀ κ) := (ssPlaces_finite p N₀ κ).to_subtype
    haveI : Nonempty ↥(ssPlaces p N₀ κ) := (ssPlaces_nonempty p N₀ hpN₀ κ).to_subtype
    exact Nat.card_pos

  obtain ⟨ν₁, ν₂, hν₁, hν₂, hm₁, hm₂⟩ := exists_restrictHom_pair_of_twoGluedSmoothCurves (k := κ)
    (baseChange (R p) (toBase N₀ p) κ) hXred (baseChange (R p) (toBase0 N₀ p) κ) (baseChange (R p) (toBase0 N₀ p) κ)
    ⟨𝔓.comp κ (algebraMap (R p) κ) 0, 𝔓.comp_over κ (algebraMap (R p) κ) 0⟩
    ⟨𝔓.comp κ (algebraMap (R p) κ) 1, 𝔓.comp_over κ (algebraMap (R p) κ) 1⟩
    (𝔓.comp_jointly_surjective κ (algebraMap (R p) κ)) (𝔓.crossing_reduced κ (algebraMap (R p) κ))
    (Nat.card ↥(ssPlaces p N₀ κ)) hcard hs0
    (sectionBaseChange κ 𝔓.εinf) (sectionBaseChange κ ε₀) hε₁' (sectionBaseChange κ ε₀)
    (D.baseChange κ) hDκ (D₀.baseChange κ) hD₀κ (D₀.baseChange κ) hD₀κ

  obtain ⟨τ, hτci, hτmul, hker⟩ := exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves (k := κ)
    (baseChange (R p) (toBase N₀ p) κ) hXred (baseChange (R p) (toBase0 N₀ p) κ) (baseChange (R p) (toBase0 N₀ p) κ)
    ⟨𝔓.comp κ (algebraMap (R p) κ) 0, 𝔓.comp_over κ (algebraMap (R p) κ) 0⟩
    ⟨𝔓.comp κ (algebraMap (R p) κ) 1, 𝔓.comp_over κ (algebraMap (R p) κ) 1⟩
    (𝔓.comp_jointly_surjective κ (algebraMap (R p) κ)) (𝔓.crossing_reduced κ (algebraMap (R p) κ))
    (Nat.card ↥(ssPlaces p N₀ κ)) hcard hs0
    (sectionBaseChange κ 𝔓.εinf) (sectionBaseChange κ ε₀) hε₁' (sectionBaseChange κ ε₀)
    (D.baseChange κ) hDκ (D₀.baseChange κ) hD₀κ (D₀.baseChange κ) hD₀κ ν₁ ν₂ hν₁ hν₂

  obtain ⟨hflat, hsurj⟩ := flat_surjective_restrictPair_of_twoGluedSmoothCurves (k := κ)
    (baseChange (R p) (toBase N₀ p) κ) hXred (baseChange (R p) (toBase0 N₀ p) κ) (baseChange (R p) (toBase0 N₀ p) κ)
    ⟨𝔓.comp κ (algebraMap (R p) κ) 0, 𝔓.comp_over κ (algebraMap (R p) κ) 0⟩
    ⟨𝔓.comp κ (algebraMap (R p) κ) 1, 𝔓.comp_over κ (algebraMap (R p) κ) 1⟩
    (𝔓.comp_jointly_surjective κ (algebraMap (R p) κ)) (𝔓.crossing_reduced κ (algebraMap (R p) κ))
    (Nat.card ↥(ssPlaces p N₀ κ)) hcard hs0
    (sectionBaseChange κ 𝔓.εinf) (sectionBaseChange κ ε₀) hε₁' (sectionBaseChange κ ε₀)
    (D.baseChange κ) hDκ (D₀.baseChange κ) hD₀κ (D₀.baseChange κ) hD₀κ ν₁ ν₂ hν₁ hν₂

  rw [Lκ] at hτmul hm₁ hm₂
  rw [L₀κ] at hm₁ hm₂ hker
  refine ⟨hcard, hs0, hDκ, hP, hD₀κ, hP₀, hε₁', τ, ![ν₁, ν₂], hν₁, (fun t a => hν₂ t a), hτci, hτmul, ?_, hflat, hsurj,
    fun t a => ?_⟩
  · intro i
    fin_cases i
    · exact fun t a b => hm₁ t a b
    · exact fun t a b => hm₂ t a b
  · exact Fin.forall_fin_two.trans (hker t a)

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_torus_abq_specialFibre
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_torus_abq_specialFibre (solution)
