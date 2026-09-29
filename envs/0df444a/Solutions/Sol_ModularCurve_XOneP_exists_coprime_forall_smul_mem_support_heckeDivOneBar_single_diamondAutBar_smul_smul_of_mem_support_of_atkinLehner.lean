-- Prove2me | solution 1 for ModularCurve.XOneP.exists_coprime_forall_smul_mem_support_heckeDivOneBar_single_diamondAutBar_smul_smul_of_mem_support_of_atkinLehner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/70a86609-fed5-5921-a985-fe5e27cfb3f2

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
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
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
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
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaOneBar_of_neZero
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_AlgebraicCurve_SemilinearAut_correspondence_smul
import Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar
import Theorems.Thm_ModularCurve_XOneP_exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
import Theorems.Thm_ModularCurve_diamondAutBar_apply_coeffEmb_modularFunctionFieldFull_eq
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_coprime_forall_smul_mem_support_heckeDivOneBar_single_diamondAutBar_smul_smul_of_mem_support_of_atkinLehner
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.ShimuraCoveringData.mk.injEq ModularCurve.ShimuraCoveringData.mk.sizeOf_spec ModularCurve.ShimuraCoveringData.LiftData.mk.sizeOf_spec ModularCurve.ShimuraCoveringData.coe_coverHom ModularCurve.ShimuraCoveringData.LiftData.mk.injEq ModularCurve.coe_inclusionBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve

namespace H3E108
open ModularCurve CongruenceSubgroup
open scoped MatrixGroups

theorem gamma1_le_gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N := by
  intro A hA
  rw [Gamma1_mem] at hA
  exact Gamma0_mem.mpr hA.2.2

theorem modularFunctionFieldFull_le_x1FunctionField (N : ℕ) [NeZero N] :
    modularFunctionFieldFull N ≤ x1FunctionField N := by
  rw [← qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  exact qExpFunctionFieldC_mono ℚ (gamma1_le_gamma0 N)

theorem coeffEmb_mem_of_eq_laurentBaseChange_x1FunctionField
    (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField N))
    (f : ↥(modularFunctionFieldFull N)) :
    coeffEmb L (f : LaurentSeries ℚ) ∈ K := by
  rw [hK]
  exact coeffEmb_mem_laurentBaseChange L (modularFunctionFieldFull_le_x1FunctionField N f.2)

theorem coeffEmb_algebraicClosure_eq_coeffMap_coeffEmb
    (L : Type*) [Field L] [Algebra ℚ L] [Algebra L (AlgebraicClosure ℚ)] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) x = coeffMap (algebraMap L (AlgebraicClosure ℚ)) (coeffEmb L x) := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

end H3E108

set_option maxHeartbeats 6400000 in
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

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσfin : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
        σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσW : ∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
          (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom))

    (hσAL : ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K),
        ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) : LaurentSeries L) =
          ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f :
            ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ))

    (hdiamConj : ∀ (d d' : ℕ), d.Coprime (M * p) → d'.Coprime (M * p) →
      ((d' : ZMod M) = (d : ZMod M)) → ((d' : ZMod p) * (d : ZMod p) = 1) →
      ∀ (θd θd' : ↥K ≃ₐ[L] ↥K),
        (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
        (x : LaurentSeries L) = (x' : LaurentSeries L) →
          ((θd x : ↥K) : LaurentSeries L) =
            ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
        (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
        (x : LaurentSeries L) = (x' : LaurentSeries L) →
          ((θd' x : ↥K) : LaurentSeries L) =
            ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
        ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L))

    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]
    :
    ∃ d : ℕ, d.Coprime (M * p) ∧
      ∀ (P Qp : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
        Qp ∈ (ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1)).support →
        SemilinearAut.ofAlgAut σbar • P ∈
          (ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ
            (Finsupp.single
              (SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • (SemilinearAut.ofAlgAut σbar • Qp)) 1)).support := by
  classical

  let Qb := AlgebraicClosure ℚ
  let α := ModularCurve.heckeAlphaOneBar Qb (M * p) p
  let β := ModularCurve.heckeBetaOneBar Qb (M * p) p
  let dia : ℕ → (↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p))) := fun c => ModularCurve.diamondAutBar (M * p) c

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    ModularCurve.isCurveOver_x1FunctionFieldBar (M * p)
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    IsCurveOver.hasPrincipalDivisors

  have hfα : FiniteAlong (AlgebraicClosure ℚ) α :=
    ModularCurve.finiteAlong_heckeAlphaOneBar_of_neZero (AlgebraicClosure ℚ) (M * p) p
  have hfβ : FiniteAlong (AlgebraicClosure ℚ) β :=
    ModularCurve.finiteAlong_heckeBetaOneBar_of_heckeBetaOneDefined (AlgebraicClosure ℚ) (M * p) p hβdef

  have hU : ∀ D, ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ D =
      Divisor.correspondence β α hβ hα D := fun D => rfl

  have H1 : ∀ (c : ℕ) (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
      SemilinearAut.ofAlgAut (dia c) • Divisor.correspondence β α hβ hα D =
        Divisor.correspondence β α hβ hα (SemilinearAut.ofAlgAut (dia c) • D) := by
    intro c D
    obtain ⟨τc, hτα, hτβ⟩ := ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar (M * p) p c
    exact (AlgebraicCurve.SemilinearAut.correspondence_smul β α hβ hα hτβ hτα D).symm

  have H2 : ∀ (c : ℕ) (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
      (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
      dia c ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ =
        ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ := fun c f hf =>
    ModularCurve.diamondAutBar_apply_coeffEmb_modularFunctionFieldFull_eq (M * p) c f hf

  have supp_smul : ∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
      (v : Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))), v ∈ (g • D).support ↔ g⁻¹ • v ∈ D.support := by
    intro g D v
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, SemilinearAut.divisor_smul_apply]

  have H1supp : ∀ (c : ℕ) (P Q : Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
      Q ∈ (Divisor.correspondence β α hβ hα (Finsupp.single P 1)).support ↔
        SemilinearAut.ofAlgAut (dia c) • Q ∈
          (Divisor.correspondence β α hβ hα (Finsupp.single (SemilinearAut.ofAlgAut (dia c) • P) 1)).support := by
    intro c P Q
    rw [← SemilinearAut.smul_single, ← H1, supp_smul, inv_smul_smul]

  obtain ⟨d, d', hd, hd', τ, W, hτAL, hWα, hWβ⟩ :=
    ModularCurve.XOneP.exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
      p M hM hpM hβdef

  have hρ : ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
      (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
      (σbar.trans τ.symm) ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ =
        ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ := by

    have hfK : ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p))),
        ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K := fun f =>
      haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩
      H3E108.coeffEmb_mem_of_eq_laurentBaseChange_x1FunctionField L (M * p) K hK f

    have hcoeff : ∀ (x : LaurentSeries ℚ),
        ModularCurve.coeffEmb (AlgebraicClosure ℚ) x =
          ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) (ModularCurve.coeffEmb L x) := fun x =>
      H3E108.coeffEmb_algebraicClosure_eq_coeffMap_coeffEmb L x
    intro f hf
    rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [hτAL f hf, hσbar _ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK f⟩ (hcoeff _), hσAL f (hfK f)]
    exact (hcoeff _).symm
  obtain ⟨e, he, hρe⟩ := ModularCurve.exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar
    p M hM hpM (σbar.trans τ.symm) hρ
  have hτe : τ * dia e = σbar := by
    apply AlgEquiv.ext
    intro x
    rw [AlgEquiv.mul_apply, ← hρe x, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

  have hρ' : ∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
      (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
      ((dia d).trans (dia d').symm) ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ =
        ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ := by
    intro f hf
    rw [AlgEquiv.trans_apply, H2 d f hf, AlgEquiv.symm_apply_eq, H2 d' f hf]
  obtain ⟨D, hD, hDe⟩ := ModularCurve.exists_coprime_forall_eq_diamondAutBar_of_forall_apply_coeffEmb_modularFunctionFieldFull_eq_x1FunctionFieldBar
    p M hM hpM ((dia d).trans (dia d').symm) hρ'
  have hDeq : (dia d')⁻¹ * dia d = dia D := by
    apply AlgEquiv.ext
    intro x
    rw [← hDe x, AlgEquiv.trans_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  refine ⟨D, hD, fun P Qp hQ => ?_⟩
  rw [hU] at hQ ⊢

  have hQe := (H1supp e P Qp).mp hQ
  have hB2 := AlgebraicCurve.Divisor.smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
    β α hβ hα hfβ hfα W (dia d' * τ) (dia d * τ)
    (fun x => by rw [AlgEquiv.mul_apply]; exact hWβ x) (fun x => by rw [AlgEquiv.mul_apply]; exact hWα x)
    (SemilinearAut.ofAlgAut (dia e) • P) (SemilinearAut.ofAlgAut (dia e) • Qp) hQe

  have key1 : SemilinearAut.ofAlgAut (dia d' * τ) * SemilinearAut.ofAlgAut (dia e) =
      SemilinearAut.ofAlgAut (dia d') * SemilinearAut.ofAlgAut σbar := by
    rw [← map_mul, mul_assoc, hτe, map_mul]
  have key2 : SemilinearAut.ofAlgAut (dia d * τ) * SemilinearAut.ofAlgAut (dia e) =
      SemilinearAut.ofAlgAut (dia d) * SemilinearAut.ofAlgAut σbar := by
    rw [← map_mul, mul_assoc, hτe, map_mul]
  rw [← mul_smul, ← mul_smul, key1, key2, mul_smul, mul_smul] at hB2

  have hB3 := (H1supp d' ((SemilinearAut.ofAlgAut (dia d'))⁻¹ • (SemilinearAut.ofAlgAut (dia d) •
      (SemilinearAut.ofAlgAut σbar • Qp))) (SemilinearAut.ofAlgAut σbar • P)).mpr (by rwa [smul_inv_smul])
  rwa [← mul_smul, ← map_inv, ← map_mul, hDeq] at hB3

#print axioms solution

end S_ModularCurve_XOneP_exists_coprime_forall_smul_mem_support_heckeDivOneBar_single_diamondAutBar_smul_smul_of_mem_support_of_atkinLehner
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_coprime_forall_smul_mem_support_heckeDivOneBar_single_diamondAutBar_smul_smul_of_mem_support_of_atkinLehner (solution)
