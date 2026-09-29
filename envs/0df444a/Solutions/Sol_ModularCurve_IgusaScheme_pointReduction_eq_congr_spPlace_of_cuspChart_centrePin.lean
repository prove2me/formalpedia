-- Prove2me | solution 1 for ModularCurve.IgusaScheme.pointReduction_eq_congr_spPlace_of_cuspChart_centrePin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1fc098fb-e758-574e-bf37-e6ddaf95aeb3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_finChart_centrePin
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_pointReduction_eq_congr_spPlace_of_cuspChart_centrePin
p2m_attr_erase "instance" "instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme

open scoped TensorProduct

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd (igusaTo p ℓ) _ = Mη.toBase)
    (hgenFin : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgFin p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
        ∀ b : ↥(chartAlgFin p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits)
    (hgenInf : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgInf p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
        ∀ b : ↥(chartAlgInf p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits)
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd (igusaTo p ℓ) _ = (Ms A hA).toBase)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ p → ModularPolynomialData d)
    (hsep : (((dataAll p (dvd_refl p)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (hCF : modularFunctionFieldC (ResidueField ↥A) p = modularFunctionFieldFullC (ResidueField ↥A) p)
    (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
    (hfin : ∀ b : chartAlgFin p ℓ,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BFin)
    (hinf : ∀ b : chartAlgInf p ℓ,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BInf)
    (hspFin : ∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _})
        (β : ↥(chartAlgFin p ℓ) →+* ResidueField ↥A),
        y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
        ∀ b : ↥(chartAlgFin p ℓ),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
            ((Ms A hA).pointEquivPlace y).toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
            ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits)
    (hspInf : ∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _})
        (β : ↥(chartAlgInf p ℓ) →+* ResidueField ↥A),
        y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
        ∀ b : ↥(chartAlgInf p ℓ),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
            ((Ms A hA).pointEquivPlace y).toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
            ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) :
    ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) (igusaTo p ℓ))
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
          q ≫ (Ms A hA).toBase = 𝟙 _}),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
        y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
        (Ms A hA).pointEquivPlace y =
          AlgebraicCurve.Place.congrRingEquiv
            (e := (IntermediateField.equivOfEq hCF).toRingEquiv)
            (he := fun a => (IntermediateField.equivOfEq hCF).commutes a)
            (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep (Mη.pointEquivPlace x)) := by
  intro xA x y hx hy

  rcases ModularCurve.IgusaScheme.exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal p ℓ xA.1 with ⟨α, hα⟩ | ⟨α, hα, hpole⟩
  · have hxf : x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (A.subtype.comp α)) ≫ ModularCurve.IgusaScheme.ιFin p ℓ := by
      rw [hx, hα, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hyf : y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp α)) ≫ ModularCurve.IgusaScheme.ιFin p ℓ := by
      rw [hy, hα, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact ModularCurve.CharPModel.FibreModel.placeFullC_eq_congr_spPlace_of_finChart_centrePin p ℓ hℓp A hA (ρ A hA) (hρ A hA)
      dataAll hsep hCF fm cc hfin hinf (Mη.pointEquivPlace x) ((Ms A hA).pointEquivPlace y) α
      (hgenFin x (A.subtype.comp α) hxf) (hspFin y ((IsLocalRing.residue ↥A).comp α) hyf)
  · have hxf : x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (A.subtype.comp α)) ≫ ModularCurve.IgusaScheme.ιInf p ℓ := by
      rw [hx, hα, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hyf : y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp α)) ≫ ModularCurve.IgusaScheme.ιInf p ℓ := by
      rw [hy, hα, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact ModularCurve.CharPModel.FibreModel.placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal p ℓ hℓp A hA (ρ A hA) (hρ A hA)
      dataAll hsep hCF fm cc hfin hinf (Mη.pointEquivPlace x) ((Ms A hA).pointEquivPlace y) α hpole
      (hgenInf x (A.subtype.comp α) hxf) (hspInf y ((IsLocalRing.residue ↥A).comp α) hyf)

end
end S_ModularCurve_IgusaScheme_pointReduction_eq_congr_spPlace_of_cuspChart_centrePin
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_pointReduction_eq_congr_spPlace_of_cuspChart_centrePin (solution)
