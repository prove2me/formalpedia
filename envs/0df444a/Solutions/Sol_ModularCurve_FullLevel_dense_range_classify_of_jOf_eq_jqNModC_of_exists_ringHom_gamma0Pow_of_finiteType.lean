-- Prove2me | solution 1 for ModularCurve.FullLevel.dense_range_classify_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/13c8bc00-6a33-50f9-a323-c1129c633336

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_FullLevel_index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow
import Theorems.Thm_ModularCurve_FullLevel_finiteDimensional_and_finrank_adjoin_le_index_of_coe_eq_jqNModC_of_eq_laurentBaseChange_levelH
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_dense_range_classify_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow_of_finiteType
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

namespace P2M
namespace DenseRange

section Fields

variable {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]

theorem comap_val_adjoin_singleton (K : IntermediateField L E) (z : ↥K) :
    (IntermediateField.adjoin L ({(z : E)} : Set E)).comap K.val = IntermediateField.adjoin L ({z} : Set ↥K) := by
  apply le_antisymm
  · intro w hw
    have hw' : (w : E) ∈ IntermediateField.adjoin L ({(z : E)} : Set E) := hw
    have hmap : IntermediateField.adjoin L ({(z : E)} : Set E) =
        (IntermediateField.adjoin L ({z} : Set ↥K)).map K.val := by
      rw [IntermediateField.adjoin_map]
      simp
    rw [hmap] at hw'
    obtain ⟨w', hw'mem, hw'eq⟩ := hw'
    have : w' = w := Subtype.ext hw'eq
    rw [← this]
    exact hw'mem
  · rw [IntermediateField.adjoin_le_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    show (K.val z) ∈ IntermediateField.adjoin L ({(z : E)} : Set E)
    exact IntermediateField.subset_adjoin L _ (Set.mem_singleton _)

theorem finrank_adjoin_singleton_eq_relfinrank (K : IntermediateField L E) (z : ↥K) :
    Module.finrank ↥(IntermediateField.adjoin L ({z} : Set ↥K)) ↥K =
      IntermediateField.relfinrank (IntermediateField.adjoin L ({(z : E)} : Set E)) K := by
  have h := IntermediateField.finrank_comap (IntermediateField.adjoin L ({(z : E)} : Set E)) K.val
  rw [IntermediateField.fieldRange_val, comap_val_adjoin_singleton] at h
  exact h

end Fields

theorem exists_mul_eq_of_mem_closure_range {B K : Type*} [CommRing B] [Field K] (φ : B →+* K)
    (k : K) (hk : k ∈ Subfield.closure (Set.range φ)) :
    ∃ a b : B, φ b ≠ 0 ∧ k * φ b = φ a := by
  rw [Subfield.mem_closure_iff] at hk
  obtain ⟨y, hy, z, hz, rfl⟩ := hk
  have hcl : Subring.closure (Set.range φ) = φ.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hcl] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  by_cases hb : φ b = 0
  · refine ⟨0, 1, ?_, ?_⟩
    · rw [map_one]; exact one_ne_zero
    · rw [hb, div_zero, map_one, map_zero, zero_mul]
  · exact ⟨a, b, hb, div_mul_cancel₀ (φ a) hb⟩

section Descent

variable {A : Type} [CommRing A] [IsDomain A] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L]
  {K₀ : Type} [Field K₀] [Algebra L K₀] [Algebra A K₀] [IsScalarTower A L K₀]
  {B : Type} [CommRing B] [Algebra A B]

theorem algebraMap_mem_closure_range (φ : B →ₐ[A] K₀) (z : L) :
    algebraMap L K₀ z ∈ Subfield.closure (Set.range φ) := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  have hs0 : algebraMap A K₀ (s : A) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A L K₀]
    intro h
    rw [map_eq_zero] at h
    exact nonZeroDivisors.ne_zero s.2 ((IsFractionRing.injective A L) (by rw [h, map_zero]))
  have hspec := IsLocalization.mk'_spec L a s
  have hspec' : algebraMap L K₀ (IsLocalization.mk' L a s) * algebraMap A K₀ (s : A) = algebraMap A K₀ a := by
    rw [IsScalarTower.algebraMap_apply A L K₀ (s : A), ← map_mul, hspec, ← IsScalarTower.algebraMap_apply]
  have heq : algebraMap L K₀ (IsLocalization.mk' L a s) = algebraMap A K₀ a * (algebraMap A K₀ (s : A))⁻¹ := by
    rw [← hspec', mul_inv_cancel_right₀ hs0]
  show algebraMap L K₀ (IsLocalization.mk' L a s) ∈ _
  rw [heq]
  refine Subfield.mul_mem _ ?_ (Subfield.inv_mem _ ?_)
  · rw [← φ.commutes a]; exact Subfield.subset_closure ⟨_, rfl⟩
  · rw [← φ.commutes (s : A)]; exact Subfield.subset_closure ⟨_, rfl⟩

noncomputable def rangeField (φ : B →ₐ[A] K₀) : IntermediateField L K₀ :=
  (Subfield.closure (Set.range φ)).toIntermediateField (algebraMap_mem_closure_range L φ)

theorem mem_rangeField_iff (φ : B →ₐ[A] K₀) (k : K₀) :
    k ∈ rangeField L φ ↔ k ∈ Subfield.closure (Set.range φ) := Iff.rfl

theorem apply_mem_rangeField (φ : B →ₐ[A] K₀) (b : B) : φ b ∈ rangeField L φ :=
  Subfield.subset_closure ⟨b, rfl⟩

noncomputable def toRangeField (φ : B →ₐ[A] K₀) : B →ₐ[A] ↥(rangeField L φ) where
  toFun b := ⟨φ b, apply_mem_rangeField L φ b⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ a b)
  map_zero' := Subtype.ext (map_zero φ)
  map_add' a b := Subtype.ext (map_add φ a b)
  commutes' a := Subtype.ext (by
    show φ (algebraMap A B a) = ((algebraMap A ↥(rangeField L φ) a : ↥(rangeField L φ)) : K₀)
    rw [φ.commutes]
    rfl)

variable {L} in

def valA (F : IntermediateField L K₀) : ↥F →ₐ[A] K₀ where
  toFun z := (z : K₀)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem valA_comp_toRangeField (φ : B →ₐ[A] K₀) : (valA (rangeField L φ)).comp (toRangeField L φ) = φ :=
  AlgHom.ext fun _ => rfl

end Descent

theorem dense_of_degree_count {A : Type} [CommRing A] [IsDomain A] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L]
    {K₀ : Type} [Field K₀] [Algebra L K₀] [Algebra A K₀] [IsScalarTower A L K₀]
    (D : LevelModuliDatum.{0} A) (P₀ : LevelModuliPackageAbs A D) (x : D.Pt K₀) (μ : ℕ)
    (hy : Transcendental L (D.jOf x))
    (hupper : FiniteDimensional ↥(IntermediateField.adjoin L ({D.jOf x} : Set K₀)) K₀ ∧
      Module.finrank ↥(IntermediateField.adjoin L ({D.jOf x} : Set K₀)) K₀ ≤ μ)
    (hlower : ∀ (T : Type) [Field T] [Algebra A T] [Algebra L T] [IsScalarTower A L T] (x' : D.Pt T),
      Transcendental L (D.jOf x') →
      FiniteDimensional ↥(IntermediateField.adjoin L ({D.jOf x'} : Set T)) T →
        μ ≤ Module.finrank ↥(IntermediateField.adjoin L ({D.jOf x'} : Set T)) T) :
    ∀ k : K₀, ∃ a b : P₀.B₀, P₀.classify x b ≠ 0 ∧ k * P₀.classify x b = P₀.classify x a := by
  obtain ⟨hfinK, hupper⟩ := hupper

  let φ : P₀.B₀ →ₐ[A] K₀ := P₀.classify x
  let F : IntermediateField L K₀ := rangeField L φ
  let xF : D.Pt ↥F := D.map (toRangeField L φ) P₀.univ
  have hxF : D.map (valA F) xF = x := by
    show D.map (valA (rangeField L φ)) (D.map (toRangeField L φ) P₀.univ) = x
    rw [← D.map_comp, valA_comp_toRangeField]
    exact P₀.map_classify x
  have hjF : ((D.jOf xF : ↥F) : K₀) = D.jOf x := by
    have h := D.jOf_map (valA F) xF
    rw [hxF] at h
    exact h.symm
  have hyF : D.jOf x ∈ F := by rw [← hjF]; exact (D.jOf xF).2

  have htr : Transcendental L (D.jOf xF) := by
    intro halg
    have h1 : IsAlgebraic L (F.val (D.jOf xF)) := halg.algHom F.val
    have h2 : F.val (D.jOf xF) = D.jOf x := hjF
    rw [h2] at h1
    exact hy h1

  let Ly : IntermediateField L K₀ := IntermediateField.adjoin L ({D.jOf x} : Set K₀)
  have hLyF : Ly ≤ F := by
    show IntermediateField.adjoin L ({D.jOf x} : Set K₀) ≤ F
    rw [IntermediateField.adjoin_le_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hyF
  have htower : IntermediateField.relfinrank Ly F * Module.finrank ↥F K₀ = Module.finrank ↥Ly K₀ :=
    IntermediateField.relfinrank_mul_finrank_top hLyF
  have hposK : 0 < Module.finrank ↥Ly K₀ := Module.finrank_pos
  have hposrel : 0 < IntermediateField.relfinrank Ly F := by
    rcases Nat.eq_zero_or_pos (IntermediateField.relfinrank Ly F) with h | h
    · rw [h, zero_mul] at htower; omega
    · exact h

  have hrel : Module.finrank ↥(IntermediateField.adjoin L ({D.jOf xF} : Set ↥F)) ↥F = IntermediateField.relfinrank Ly F := by
    rw [finrank_adjoin_singleton_eq_relfinrank F (D.jOf xF), hjF]
  have hfinF : FiniteDimensional ↥(IntermediateField.adjoin L ({D.jOf xF} : Set ↥F)) ↥F := by
    apply Module.finite_of_finrank_pos
    rw [hrel]; exact hposrel

  have hlow := hlower ↥F xF htr hfinF
  rw [hrel] at hlow

  have hFK1 : Module.finrank ↥F K₀ = 1 := by
    have h1 : IntermediateField.relfinrank Ly F * Module.finrank ↥F K₀ ≤ IntermediateField.relfinrank Ly F * 1 := by
      rw [htower, mul_one]; exact hupper.trans hlow
    have h2 : Module.finrank ↥F K₀ ≤ 1 := Nat.le_of_mul_le_mul_left h1 hposrel
    have hposFK : 0 < Module.finrank ↥F K₀ := by
      rcases Nat.eq_zero_or_pos (Module.finrank ↥F K₀) with h | h
      · rw [h, mul_zero] at htower; omega
      · exact h
    omega
  have hFtop : F = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp hFK1

  intro k
  have hk : k ∈ F := by rw [hFtop]; exact IntermediateField.mem_top
  exact exists_mul_eq_of_mem_closure_range φ.toRingHom k hk

end P2M.DenseRange

open P2M.DenseRange in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ)) :
    ∀ k : ↥K, ∃ a b : P₀.B₀, P₀.classify x b ≠ 0 ∧ k * P₀.classify x b = P₀.classify x a := by
  refine dense_of_degree_count L (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum P₀ x
    ((CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index) ?_ ?_ ?_
  ·
    intro halg
    have h1 := halg.algHom K.val
    have h2 : K.val ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x) = ModularCurve.jqNModC L (q * ℓ) := hx
    rw [h2] at h1
    exact ModularCurve.transcendental_jqNModC L (q * ℓ) h1
  ·
    exact ModularCurve.FullLevel.finiteDimensional_and_finrank_adjoin_le_index_of_coe_eq_jqNModC_of_eq_laurentBaseChange_levelH
      (q * ℓ) M' L K hK j hj _ hx
  ·
    intro T _ _ _ _ x' htr hfin
    exact ModularCurve.FullLevel.index_le_finrank_adjoin_jOf_of_transcendental_jOf_rigidDataPow q M' hqM' ℓ hℓ3 hℓq hℓM' L A
      hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO T x' htr hfin

end S_ModularCurve_FullLevel_dense_range_classify_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow_of_finiteType
end P2MW
export P2MW.S_ModularCurve_FullLevel_dense_range_classify_of_jOf_eq_jqNModC_of_exists_ringHom_gamma0Pow_of_finiteType (solution)
