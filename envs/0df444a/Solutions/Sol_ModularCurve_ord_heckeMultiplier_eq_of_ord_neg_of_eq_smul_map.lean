-- Prove2me | solution 1 for ModularCurve.ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f2e76951-1dd7-5bb8-8253-c2314feb9372

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_ModularCurve_ord_heckeMultiplier_eq_zero_of_evalAt_ne
import Theorems.Thm_ModularCurve_ord_heckeMultiplier_eq_of_ord_neg
import Theorems.Thm_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve KaehlerDifferential

namespace FltWs24
namespace FD

open ModularCurve AlgebraicCurve

theorem fdC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    FiniteDimensional ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  exact CharPModel.finiteDimensional_adjoin_jLine k N data

theorem fdR (k : Type*) [Field k] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    FiniteDimensional ↥(IntermediateField.adjoin k ({heckeAlphaC k N ℓ (jGeomGen k N)} : Set ↥(charLDegeneracyRoof k N ℓ))) ↥(charLDegeneracyRoof k N ℓ) := by
  set E : IntermediateField k ↥(modularFunctionFieldC k N) := IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N)) with hE
  haveI : FiniteDimensional ↥E ↥(modularFunctionFieldC k N) := fdC k N

  letI := AlgebraicCurve.algebraAlong (heckeAlphaC k N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC k N ℓ)
  haveI : Module.Finite ↥(modularFunctionFieldC k N) ↥(charLDegeneracyRoof k N ℓ) := finiteAlong_heckeAlphaC k N ℓ

  letI : Algebra ↥E ↥(charLDegeneracyRoof k N ℓ) := ((algebraMap ↥(modularFunctionFieldC k N) ↥(charLDegeneracyRoof k N ℓ)).comp (algebraMap ↥E ↥(modularFunctionFieldC k N))).toAlgebra
  haveI : IsScalarTower ↥E ↥(modularFunctionFieldC k N) ↥(charLDegeneracyRoof k N ℓ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hER : Module.Finite ↥E ↥(charLDegeneracyRoof k N ℓ) := Module.Finite.trans ↥(modularFunctionFieldC k N) ↥(charLDegeneracyRoof k N ℓ)

  have hmap : E.map (heckeAlphaC k N ℓ) = IntermediateField.adjoin k ({heckeAlphaC k N ℓ (jGeomGen k N)} : Set ↥(charLDegeneracyRoof k N ℓ)) := by
    rw [hE, IntermediateField.adjoin_map, Set.image_singleton]
  let e : ↥E ≃ₐ[k] ↥(E.map (heckeAlphaC k N ℓ)) := E.equivMap (heckeAlphaC k N ℓ)
  letI : Algebra ↥E ↥(E.map (heckeAlphaC k N ℓ)) := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower ↥E ↥(E.map (heckeAlphaC k N ℓ)) ↥(charLDegeneracyRoof k N ℓ) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hfin : Module.Finite ↥(E.map (heckeAlphaC k N ℓ)) ↥(charLDegeneracyRoof k N ℓ) :=
    Module.Finite.of_restrictScalars_finite ↥E _ _
  rw [hmap] at hfin
  exact hfin

end FltWs24.FD

theorem solution
    (k : Type*) [Field k] [PerfectField k] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    [AlgebraicCurve.IsCurveOver k ↥(modularFunctionFieldC k N)] [AlgebraicCurve.IsCurveOver k ↥(charLDegeneracyRoof k N ℓ)]
    [∀ v : Place k ↥(modularFunctionFieldC k N), v.DCoordGenerates] [∀ w : Place k ↥(charLDegeneracyRoof k N ℓ), w.DCoordGenerates]
    (h : ↥(charLDegeneracyRoof k N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC k N ℓ)
      haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC k N ℓ)
      KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N))
        = h • KaehlerDifferential.map k k ↥(modularFunctionFieldC k N) ↥(charLDegeneracyRoof k N ℓ)
            (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N)))
    (hDα : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeAlphaC k N ℓ (jGeomGen k N)) ≠ 0)
    (hDβ : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N)) ≠ 0)
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hyα : y.ord (heckeAlphaC k N ℓ (jGeomGen k N)) < 0)
    (htα : ((y.ord (heckeAlphaC k N ℓ (jGeomGen k N))).natAbs : k) ≠ 0)
    (htβ : ((y.ord (heckeBetaC k N ℓ (jGeomGen k N))).natAbs : k) ≠ 0) :
    y.ord h = y.ord (heckeBetaC k N ℓ (jGeomGen k N)) - y.ord (heckeAlphaC k N ℓ (jGeomGen k N)) := by
  haveI : FiniteDimensional ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) :=
    FltWs24.FD.fdC k N
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : FiniteDimensional ↥(IntermediateField.adjoin k ({heckeAlphaC k N ℓ (jGeomGen k N)} : Set ↥(charLDegeneracyRoof k N ℓ))) ↥(charLDegeneracyRoof k N ℓ) :=
    FltWs24.FD.fdR k N ℓ
  have hD' : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N))
      = h • pullbackDiff (heckeAlphaC k N ℓ) (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N)) := hD
  exact ModularCurve.ord_heckeMultiplier_eq_of_ord_neg k N ℓ hℓN h hD' hDα hDβ y hyα htα htβ

end S_ModularCurve_ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map
end P2MW
export P2MW.S_ModularCurve_ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map (solution)
