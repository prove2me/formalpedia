-- Prove2me | solution 1 for ModularCurve.IsModuliPlaceOf.mem_nonunits_iff_of_isIntegral_jModElt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a5800363-4e97-52b8-b617-98f1e951104e

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_and_reduceHom_vcFun_eq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_ModuliPoint_mk_eq_mk_iff_step
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring
import Theorems.Thm_AlgebraicCurve_Place_exists_valuationSubring_algHom_apply_eq_forall_mem_iff
import Theorems.Thm_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqNFull jqNFull_one ModuliTestDatum IsModuliPlaceOf ModuliTestDatum.place_toValuationSubring divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC jqNModC jModElt mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map_mk ModuliPoint.map_comp Gamma0Pair ModuliPoint ModuliPoint.j Point.heq_nsmul exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ ModuliPoint.mk_eq_mk_iff_step transcendental_jqModC"
p2m_open "ModularCurve"
namespace ModuliPlaceUnique

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve Polynomial
open scoped IntermediateField Pointwise

section PlaceTools

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

theorem mem_nonunits_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) :
    f ∈ v.toValuationSubring.nonunits := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (v.toValuationSubring.nonunits).zero_mem
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have hmem : f ∈ v.toValuationSubring := by
    rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
      zpow_natCast]
    exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hmem, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have h0 := v.ord_coe_unit hunit.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord f = 0 at h0
  omega

theorem mem_iff_of_smul_eq {E : IntermediateField K F} {W₀ : Place K F} {σ : F ≃ₐ[E] F}
    (hσ : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀) (m : F) :
    σ m ∈ W₀.toValuationSubring ↔ m ∈ W₀.toValuationSubring := by
  have hO : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀.toValuationSubring =
      W₀.toValuationSubring := by
    rw [← SemilinearAut.smul_toValuationSubring, hσ]
  constructor
  · intro hm
    have h1 : (SemilinearAut.ofAlgAut (σ.restrictScalars K))⁻¹ • σ m ∈
        (SemilinearAut.ofAlgAut (σ.restrictScalars K))⁻¹ • W₀.toValuationSubring :=
      ValuationSubring.smul_mem_pointwise_smul _ _ _ hm
    rw [inv_smul_eq_iff.mpr hO.symm] at h1
    have h2 : (SemilinearAut.ofAlgAut (σ.restrictScalars K))⁻¹ • σ m = m := by
      rw [inv_smul_eq_iff, SemilinearAut.ofAlgAut_smul]
      rfl
    rwa [h2] at h1
  · intro hm
    have h1 := ValuationSubring.smul_mem_pointwise_smul
      (SemilinearAut.ofAlgAut (σ.restrictScalars K)) m W₀.toValuationSubring hm
    rw [hO, SemilinearAut.ofAlgAut_smul] at h1
    exact h1

omit [Algebra K F] in
variable (K) in
lemma adjoin_toSubring_eq_closure [Algebra K F] (t : F) :
    (Algebra.adjoin K ({t} : Set F)).toSubring =
      Subring.closure (Set.range ((algebraMap K F).comp (⊤ : ValuationSubring K).subtype) ∪ {t}) := by
  have hr : Set.range ((algebraMap K F).comp (⊤ : ValuationSubring K).subtype) =
      Set.range (algebraMap K F) := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, ValuationSubring.mem_top a⟩, rfl⟩
  rw [hr]
  ext x
  rw [Subalgebra.mem_toSubring, Algebra.mem_adjoin_iff]

variable (K) in

lemma exists_place_ord_pos [IsAlgClosed K] (t : F) (htr : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]
    (j₀ : K) : ∃ W₀ : Place K F, 0 < W₀.ord (t - algebraMap K F j₀) := by
  let A : ValuationSubring K := ⊤
  let B : Subring F := (Algebra.adjoin K ({t} : Set F)).toSubring
  have hconst : ∀ a : A, algebraMap K F a ∈ B := fun a =>
    (Algebra.adjoin K ({t} : Set F)).algebraMap_mem a
  have htB : t ∈ B := Algebra.self_mem_adjoin_singleton K t
  have hint : ∀ b : B, IsIntegral
      (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {t})) (b : F) := by
    intro b
    have hb : (b : F) ∈ Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {t}) := by
      rw [← adjoin_toSubring_eq_closure]; exact b.2
    exact isIntegral_algebraMap (A := F)
      (x := (⟨(b : F), hb⟩ : Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {t})))
  let g : B := ⟨t, htB⟩ - ⟨algebraMap K F j₀, hconst ⟨j₀, ValuationSubring.mem_top j₀⟩⟩
  have hg : ¬ IsUnit g := by
    intro hu
    let e := Polynomial.algEquivOfTranscendental K t htr
    have hge : e (Polynomial.X - Polynomial.C j₀) = g := by
      apply Subtype.ext
      simp [e, g, Polynomial.algEquivOfTranscendental_apply]
    have : IsUnit (Polynomial.X - Polynomial.C j₀ : Polynomial K) := by
      rw [← hge] at hu
      exact (MulEquiv.isUnit_map e).mp hu
    exact Polynomial.not_isUnit_X_sub_C j₀ this
  obtain ⟨𝔮, h𝔮max, hg𝔮⟩ := Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_ne_top hg)
  haveI : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A →
      (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      apply (IsLocalRing.mem_maximalIdeal _).mp ha
      have hne' : (a : K) ≠ 0 := fun h => hne (Subtype.ext h)
      exact ⟨⟨a, ⟨(a : K)⁻¹, ValuationSubring.mem_top _⟩,
        Subtype.ext (mul_inv_cancel₀ hne'), Subtype.ext (inv_mul_cancel₀ hne')⟩, rfl⟩
    have : (⟨algebraMap K F a, hconst a⟩ : B) = 0 := by
      apply Subtype.ext; simp [ha0]
    rw [this]; exact 𝔮.zero_mem
  have hja : (⟨t, htB⟩ : B) - ⟨algebraMap K F ((⟨j₀, ValuationSubring.mem_top j₀⟩ : A) : K),
      hconst _⟩ ∈ 𝔮 := hg𝔮 (Ideal.mem_span_singleton_self g)
  obtain ⟨w, hw, -⟩ := AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring A htr hconst htB
    hint 𝔮 h𝔮A ⟨j₀, ValuationSubring.mem_top j₀⟩ hja
  exact ⟨w, hw⟩

end PlaceTools

section Cast

variable {K' : Type*} [Field K'] [DecidableEq K']

def castHom {W W' : WeierstrassCurve K'} (h : W = W') : W.toAffine.Point →+ W'.toAffine.Point where
  toFun v := h ▸ v
  map_zero' := by subst h; rfl
  map_add' := by subst h; intros; rfl

theorem castHom_some {W W' : WeierstrassCurve K'} (h : W = W') (x y : K')
    (hx : W.toAffine.Nonsingular x y) :
    castHom h (.some x y hx) = .some x y (h ▸ hx) := by subst h; rfl

theorem castHom_injective {W W' : WeierstrassCurve K'} (h : W = W') :
    Function.Injective (castHom h) := by subst h; exact fun a b hab => hab

theorem heq_castHom {W W' : WeierstrassCurve K'} (h : W = W') (P : W.toAffine.Point) :
    HEq (castHom h P) P := by subst h; rfl

theorem castHom_castHom_symm {W W' : WeierstrassCurve K'} (h : W = W') (P : W'.toAffine.Point) :
    castHom h (castHom h.symm P) = P := by subst h; rfl

theorem castHom_symm_castHom {W W' : WeierstrassCurve K'} (h : W = W') (P : W.toAffine.Point) :
    castHom h.symm (castHom h P) = P := by subst h; rfl

theorem eq_castHom_of_heq {W W' : WeierstrassCurve K'} (h : W = W') {P : W.toAffine.Point}
    {P' : W'.toAffine.Point} (hP : HEq P' P) : P' = castHom h P := by
  subst h; exact eq_of_heq hP

theorem addOrderOf_castHom {W W' : WeierstrassCurve K'} (h : W = W') (P : W.toAffine.Point) :
    addOrderOf (castHom h P) = addOrderOf P :=
  addOrderOf_injective (castHom h) (castHom_injective h) P

theorem cyclicQuotientJ_map_castHom {W W' : WeierstrassCurve K'} (h : W = W')
    (H : AddSubgroup W.toAffine.Point) (N : ℕ) :
    W'.cyclicQuotientJ (H.map (castHom h)) N = W.cyclicQuotientJ H N := by
  subst h
  congr 1
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩; exact hQ
  · intro hP; exact ⟨P, hP, rfl⟩

theorem gamma0Pair_eq {N : ℕ} {P Q : Gamma0Pair N K'} (h1 : P.toCurve = Q.toCurve)
    (h2 : HEq P.gen Q.gen) : P = Q := by
  obtain ⟨c, e, g, o⟩ := P
  obtain ⟨c', e', g', o'⟩ := Q
  cases h1
  cases h2
  rfl

end Cast

section MapPt

variable {K K' : Type*} [Field K] [Field K'] [DecidableEq K] [DecidableEq K']

def mapPt (f : K →+* K') {V : WeierstrassCurve K} {V' : WeierstrassCurve K'} (h : V.map f = V') :
    V.toAffine.Point →+ V'.toAffine.Point :=
  (castHom h).comp (WeierstrassCurve.mapPointHom f (W₀ := V))

omit [DecidableEq K] [DecidableEq K'] in
theorem map_nonsingular_of_eq (f : K →+* K') {V : WeierstrassCurve K} {V' : WeierstrassCurve K'}
    (h : V.map f = V') {x y : K} (hxy : V.toAffine.Nonsingular x y) :
    V'.toAffine.Nonsingular (f x) (f y) := by
  subst h; exact (V.toAffine.map_nonsingular f.injective x y).mpr hxy

theorem mapPt_some (f : K →+* K') {V : WeierstrassCurve K} {V' : WeierstrassCurve K'}
    (h : V.map f = V') {x y : K} (hxy : V.toAffine.Nonsingular x y) :
    mapPt f h (.some x y hxy) = .some (f x) (f y) (map_nonsingular_of_eq f h hxy) := by
  subst h; rfl

theorem mapPt_apply (f : K →+* K') {V : WeierstrassCurve K} {V' : WeierstrassCurve K'}
    (h : V.map f = V') (P : V.toAffine.Point) :
    mapPt f h P = castHom h (WeierstrassCurve.mapPoint f (W₀ := V) P) :=
  rfl

theorem mapPt_injective (f : K →+* K') {V : WeierstrassCurve K} {V' : WeierstrassCurve K'}
    (h : V.map f = V') : Function.Injective (mapPt f h) :=
  (castHom_injective h).comp (WeierstrassCurve.mapPoint_injective f)

omit [DecidableEq K'] in
theorem heq_mapPoint_castHom (f : K →+* K') {V V' : WeierstrassCurve K} (h : V = V')
    (P : V.toAffine.Point) :
    HEq (WeierstrassCurve.mapPoint f (W₀ := V') (castHom h P))
      (WeierstrassCurve.mapPoint f (W₀ := V) P) := by
  subst h; rfl

end MapPt

section VC

variable {F : Type*} [Field F] [DecidableEq F]

def vcInvHom (C : VariableChange F) (W : WeierstrassCurve.Affine F) :
    W.Point →+ (C • W).toAffine.Point where
  toFun := Point.vcInvFun C W
  map_zero' := rfl
  map_add' := WeierstrassCurve.Affine.Point.vcInvFun_add C W

@[scoped simp] theorem vcInvHom_apply (C : VariableChange F) (W : WeierstrassCurve.Affine F) (P : W.Point) :
    vcInvHom C W P = Point.vcInvFun C W P := rfl

theorem vcInvFun_injective (C : VariableChange F) (W : WeierstrassCurve.Affine F) :
    Function.Injective (Point.vcInvFun C W) :=
  (Point.vcFun_rightInverse (C := C) (W := W)).injective

theorem vcFun_injective (C : VariableChange F) (W : WeierstrassCurve.Affine F) :
    Function.Injective (Point.vcFun C W) :=
  (Point.vcFun_leftInverse (C := C) (W := W)).injective

theorem vcFun_add (C : VariableChange F) (W : WeierstrassCurve.Affine F) (P Q : (C • W).toAffine.Point) :
    Point.vcFun C W (P + Q) = Point.vcFun C W P + Point.vcFun C W Q := by
  apply vcInvFun_injective C W
  rw [Point.vcInvFun_add, Point.vcFun_leftInverse, Point.vcFun_leftInverse, Point.vcFun_leftInverse]

def vcHom (C : VariableChange F) (W : WeierstrassCurve.Affine F) :
    (C • W).toAffine.Point →+ W.Point where
  toFun := Point.vcFun C W
  map_zero' := rfl
  map_add' := vcFun_add C W

@[scoped simp] theorem vcHom_apply (C : VariableChange F) (W : WeierstrassCurve.Affine F)
    (P : (C • W).toAffine.Point) : vcHom C W P = Point.vcFun C W P := rfl

theorem vcFun_nsmul (C : VariableChange F) (W : WeierstrassCurve.Affine F) (n : ℕ)
    (P : (C • W).toAffine.Point) : Point.vcFun C W (n • P) = n • Point.vcFun C W P :=
  map_nsmul (vcHom C W) n P

theorem vcInvFun_nsmul (C : VariableChange F) (W : WeierstrassCurve.Affine F) (n : ℕ) (P : W.Point) :
    Point.vcInvFun C W (n • P) = n • Point.vcInvFun C W P :=
  map_nsmul (vcInvHom C W) n P

theorem addOrderOf_vcInvFun (C : VariableChange F) (W : WeierstrassCurve.Affine F) (P : W.Point) :
    addOrderOf (Point.vcInvFun C W P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom C W) (vcInvFun_injective C W) P

theorem addOrderOf_vcFun (C : VariableChange F) (W : WeierstrassCurve.Affine F)
    (P : (C • W).toAffine.Point) : addOrderOf (Point.vcFun C W P) = addOrderOf P :=
  addOrderOf_injective (vcHom C W) (vcFun_injective C W) P

theorem mem_zmultiples_vcInvFun_iff (γ : VariableChange F) (W : WeierstrassCurve F)
    (g : W.toAffine.Point) (P' : (γ • W).toAffine.Point) :
    P' ∈ AddSubgroup.zmultiples (Point.vcInvFun γ W.toAffine g) ↔
      Point.vcFun γ W.toAffine P' ∈ AddSubgroup.zmultiples g := by
  constructor
  · intro hP'
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP'
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
    have h1 : (m • Point.vcInvFun γ W.toAffine g) = vcInvHom γ W.toAffine (m • g) := by
      rw [map_zsmul]; rfl
    rw [h1, vcInvHom_apply]
    exact (Point.vcFun_rightInverse (m • g)).symm
  · intro hP'
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hP'
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
    have h1 : Point.vcInvFun γ W.toAffine (Point.vcFun γ W.toAffine P') = P' :=
      Point.vcFun_leftInverse P'
    rw [← h1, ← hm]
    change m • Point.vcInvFun γ W.toAffine g = vcInvHom γ W.toAffine (m • g)
    rw [map_zsmul]; rfl

theorem cyclicQuotientJ_smul_zmultiples {N : ℕ} (hN : (N : F) ≠ 0)
    (γ : VariableChange F) (W : WeierstrassCurve F) (Q : (γ • W).toAffine.Point) :
    (γ • W).cyclicQuotientJ (AddSubgroup.zmultiples Q) N =
      W.cyclicQuotientJ (AddSubgroup.zmultiples (Point.vcFun γ W.toAffine Q)) N := by
  have hQ : Q = Point.vcInvFun γ W.toAffine (Point.vcFun γ W.toAffine Q) :=
    (Point.vcFun_leftInverse Q).symm
  conv_lhs => rw [hQ]
  exact WeierstrassCurve.cyclicQuotientJ_variableChange_eq γ W (AddSubgroup.zmultiples _) _
    (mem_zmultiples_vcInvFun_iff γ W _) N hN

end VC

section Torsion

theorem natCard_torsion {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (V : WeierstrassCurve F) [V.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) :
    Nat.card {P : V.toAffine.Point // N • P = 0} = N ^ 2 := by
  obtain ⟨e⟩ := V.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := F) hN
  have hbc : V.baseChange F = V := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hcongr : ∀ {V₁ V₂ : WeierstrassCurve F}, V₁ = V₂ →
      Nat.card {P : V₁.toAffine.Point // N • P = 0} = Nat.card {P : V₂.toAffine.Point // N • P = 0} := by
    intro V₁ V₂ h; subst h; rfl
  rw [← hcongr hbc]
  have e2 : {P : (V.baseChange F).toAffine.Point // N • P = 0} ≃
      Submodule.torsionBy ℤ (V.baseChange F).toAffine.Point N :=
    Equiv.subtypeEquivRight fun P => by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  rw [Nat.card_congr e2, ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

theorem exists_mapPoint_eq_of_nsmul_eq_zero {F Ω' : Type*} [Field F] [DecidableEq F]
    [Field Ω'] [DecidableEq Ω'] [IsAlgClosed Ω'] (f : F →+* Ω')
    (V : WeierstrassCurve F) [V.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : Ω') ≠ 0)
    (hcard : Nat.card {P : V.toAffine.Point // N • P = 0} = N ^ 2)
    (Q : (V.map f).toAffine.Point) (hQ : N • Q = 0) :
    ∃ P : V.toAffine.Point, N • P = 0 ∧ WeierstrassCurve.mapPoint f (W₀ := V) P = Q := by
  let g : {P : V.toAffine.Point // N • P = 0} → {Q : (V.map f).toAffine.Point // N • Q = 0} :=
    fun P => ⟨WeierstrassCurve.mapPointHom f (W₀ := V) P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hinj : Function.Injective g := by
    intro P₁ P₂ h
    exact Subtype.ext (WeierstrassCurve.mapPoint_injective f (congrArg Subtype.val h))
  have hc2 : Nat.card {Q : (V.map f).toAffine.Point // N • Q = 0} = N ^ 2 := natCard_torsion _ hN
  haveI : Finite {Q : (V.map f).toAffine.Point // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hc2]; exact pow_ne_zero 2 (NeZero.ne N))
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by rw [hcard, hc2])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

end Torsion

section Groups

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem zmultiples_nsmul_eq_of_coprime {g : A} {k N : ℕ}
    (hg : N • g = 0) (hk : k.Coprime N) :
    AddSubgroup.zmultiples (k • g) = AddSubgroup.zmultiples g := by
  apply le_antisymm
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) k
  · rw [AddSubgroup.zmultiples_le]
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + b * N = 1 := by
      have : IsCoprime (k : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hk
      obtain ⟨a, b, h⟩ := this
      exact ⟨a, b, h⟩
    have hN : (N : ℤ) • g = 0 := by rw [natCast_zsmul, hg]
    have key : a • (k • g) = g := by
      have e1 : (a * k + b * N) • g = g := by rw [hab, one_zsmul]
      rw [add_zsmul, mul_zsmul, mul_zsmul g b, hN, zsmul_zero, add_zero, natCast_zsmul] at e1
      exact e1
    have hmem := AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples (k • g)) a
    rwa [key] at hmem

theorem zmultiples_eq_of_map_eq (θ : A →+ B) {N : ℕ}
    (hθ : ∀ P : A, N • P = 0 → θ P = 0 → P = 0) {P Q : A} (hP : N • P = 0) (hQ : N • Q = 0)
    (h : AddSubgroup.zmultiples (θ P) = AddSubgroup.zmultiples (θ Q)) :
    AddSubgroup.zmultiples P = AddSubgroup.zmultiples Q := by
  have key : ∀ {P Q : A}, N • P = 0 → N • Q = 0 →
      AddSubgroup.zmultiples (θ P) ≤ AddSubgroup.zmultiples (θ Q) →
      AddSubgroup.zmultiples P ≤ AddSubgroup.zmultiples Q := by
    intro P Q hP hQ hle
    have hmem : θ P ∈ AddSubgroup.zmultiples (θ Q) := hle (AddSubgroup.mem_zmultiples _)
    rw [← AddMonoidHom.map_zmultiples] at hmem
    obtain ⟨R, hR, hRP⟩ := hmem
    have hNR : N • R = 0 := by
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
      rw [← natCast_zsmul, smul_comm, natCast_zsmul, hQ, zsmul_zero]
    have hPR : P = R := by
      have h1 : θ (P - R) = 0 := by rw [map_sub, hRP, sub_self]
      have h2 : N • (P - R) = 0 := by rw [nsmul_sub, hP, hNR, sub_zero]
      exact sub_eq_zero.mp (hθ _ h2 h1)
    rw [AddSubgroup.zmultiples_le, hPR]
    exact hR
  exact le_antisymm (key hP hQ h.le) (key hQ hP h.ge)

end Groups

section Over

variable {L : Type*} [Field L] {L' : Type*} [Field L']

def overHom (f : L →+* L') (A : ValuationSubring L) (O : ValuationSubring L')
    (h : ∀ a, f a ∈ O ↔ a ∈ A) : A →+* O where
  toFun a := ⟨f a, (h a).2 a.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f (a : L) (b : L))
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : L) (b : L))

variable (f : L →+* L') (A : ValuationSubring L) (O : ValuationSubring L')
  (h : ∀ a, f a ∈ O ↔ a ∈ A)

@[scoped simp] theorem coe_overHom (a : A) : ((overHom f A O h a : O) : L') = f a := rfl

theorem subtype_comp_overHom : O.subtype.comp (overHom f A O h) = f.comp A.subtype :=
  RingHom.ext fun _ => rfl

scoped instance isLocalHom_overHom : IsLocalHom (overHom f A O h) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 ha
  have hy' : f a * (y : L') = 1 := by
    have := congrArg (fun z : O => (z : L')) hy
    simpa using this
  have ha0 : (a : L) ≠ 0 := fun h0 => by
    rw [h0, map_zero, zero_mul] at hy'
    exact zero_ne_one hy'
  have hinvO : (f a)⁻¹ ∈ O := by
    rw [← (eq_inv_of_mul_eq_one_right hy')]; exact y.2
  have hinvA : (a : L)⁻¹ ∈ A := by rw [← h, map_inv₀]; exact hinvO
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinvA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

def overRes : ResidueField A →+* ResidueField O :=
  ResidueField.map (overHom f A O h)

theorem overRes_residue (a : A) : overRes f A O h (residue A a) = residue _ (overHom f A O h a) := rfl

theorem residue_comp_overHom :
    (residue O).comp (overHom f A O h) = (overRes f A O h).comp (residue A) :=
  RingHom.ext fun _ => rfl

theorem residue_overHom_eq_zero_of_mem_nonunits {a : L} (ha : a ∈ A.nonunits) :
    residue O ⟨f a, (h a).2 (A.nonunits_subset ha)⟩ = 0 := by
  have hmax : (⟨a, A.nonunits_subset ha⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp ha
  have : overHom f A O h ⟨a, A.nonunits_subset ha⟩ ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax ⊢
    exact fun hu => hmax ((isUnit_map_iff (overHom f A O h) _).1 hu)
  exact (IsLocalRing.residue_eq_zero_iff _).2 this

theorem map_overHom_map_subtype (WA : WeierstrassCurve A) :
    (WA.map A.subtype).map f = (WA.map (overHom f A O h)).map O.subtype := by
  change WA.map (f.comp A.subtype) = WA.map (O.subtype.comp (overHom f A O h))
  rw [subtype_comp_overHom]

theorem map_overHom_map_residue (WA : WeierstrassCurve A) :
    (WA.map (residue A)).map (overRes f A O h) =
      (WA.map (overHom f A O h)).map (residue O) := by
  change WA.map ((overRes f A O h).comp (residue A)) = WA.map ((residue O).comp (overHom f A O h))
  rw [residue_comp_overHom]

variable [DecidableEq L] [DecidableEq L'] [DecidableEq (ResidueField A)] [DecidableEq (ResidueField O)]

omit [DecidableEq L] [DecidableEq L'] [DecidableEq (ResidueField A)] [DecidableEq (ResidueField O)] in
theorem reduceHom_apply' {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    [DecidableEq L] [DecidableEq (ResidueField A)]
    (P : (W.map A.subtype).toAffine.Point) : reduceHom hΔ P = reducePoint hΔ P := rfl

theorem reduceHom_mapPt (WA : WeierstrassCurve A) (hΔ : (WA.map (residue A)).Δ ≠ 0)
    (hΔ' : ((WA.map (overHom f A O h)).map (residue O)).Δ ≠ 0)
    (P : (WA.map A.subtype).toAffine.Point) :
    reduceHom hΔ' (mapPt f (map_overHom_map_subtype f A O h WA) P) =
      mapPt (overRes f A O h) (map_overHom_map_residue f A O h WA) (reduceHom hΔ P) := by
  cases P with
  | zero =>
    change reduceHom hΔ' (mapPt f (map_overHom_map_subtype f A O h WA) 0) =
      mapPt (overRes f A O h) (map_overHom_map_residue f A O h WA) (reduceHom hΔ 0)
    rw [map_zero, map_zero, map_zero, map_zero]
  | some x y hxy =>
    rw [mapPt_some, reduceHom_apply', reduceHom_apply']
    by_cases hx : x ∈ A
    · have hx' : f x ∈ O := (h x).2 hx
      rw [reducePoint_some_of_mem hΔ' _ hx', reducePoint_some_of_mem hΔ hxy hx, mapPt_some]
      exact Affine.Point.some_congr' rfl rfl _ _
    · have hx' : f x ∉ O := fun h' => hx ((h x).1 h')
      rw [reducePoint_some_of_notMem hΔ' _ hx', reducePoint_some_of_notMem hΔ hxy hx, map_zero]

end Over

section ResidueK

variable {K : Type*} [Field K] [IsAlgClosed K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  {Ω' : Type*} [Field Ω'] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω']

theorem exists_ringHom_residueField [Algebra.IsAlgebraic Ω Ω'] (W : Place K Ω)
    (res : ResidueField W.toValuationSubring →+* K)
    (hres : ∀ c : K, res (algebraMap K (ResidueField W.toValuationSubring) c) = c)
    (O : ValuationSubring Ω') (hO : ∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ W.toValuationSubring)
    {M : Type*} [Field M] [Algebra K M] (W₀ : Place K M) (ι : M →ₐ[K] Ω')
    (hι : ∀ m, (ι : M →+* Ω') m ∈ O ↔ m ∈ W₀.toValuationSubring)
    (e : ResidueField W₀.toValuationSubring ≃+* K)
    (he : ∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c) :
    ∃ ē : ResidueField O →+* K,
      (∀ y, ē (overRes (algebraMap Ω Ω') W.toValuationSubring O hO y) = res y) ∧
      (∀ y, ē (overRes (ι : M →+* Ω') W₀.toValuationSubring O hι y) = e y) := by
  classical
  have hKO : ∀ c : K, algebraMap K Ω' c ∈ O := fun c => by
    rw [IsScalarTower.algebraMap_apply K Ω Ω', hO]; exact W.algebraMap_mem' c
  letI algKO : Algebra K O := ((algebraMap K Ω').codRestrict O.toSubring hKO).toAlgebra
  have halgKO : ∀ c : K, ((algebraMap K O c : O) : Ω') = algebraMap K Ω' c := fun _ => rfl

  have hresA : ∀ a : Ω, a ∈ W.toValuationSubring → ∃ c : K, a - algebraMap K Ω c ∈ W.toValuationSubring.nonunits := by
    intro a ha
    refine ⟨res (residue W.toValuationSubring ⟨a, ha⟩), ?_⟩
    have hmem : a - algebraMap K Ω (res (residue W.toValuationSubring ⟨a, ha⟩)) ∈ W.toValuationSubring :=
      sub_mem ha (W.algebraMap_mem' _)
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨hmem, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff]
    have heq : (⟨a - algebraMap K Ω (res (residue W.toValuationSubring ⟨a, ha⟩)), hmem⟩ : W.toValuationSubring) =
        ⟨a, ha⟩ - algebraMap K W.toValuationSubring (res (residue W.toValuationSubring ⟨a, ha⟩)) := Subtype.ext rfl
    rw [heq, map_sub, sub_eq_zero]

    apply res.injective
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply, hres]

  have hsurj : Function.Surjective (algebraMap K (ResidueField O)) := by
    intro y
    obtain ⟨zO, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, hc⟩ := ValuationSubring.exists_sub_algebraMap_mem_nonunits_of_isAlgebraic
      W.toValuationSubring W.algebraMap_mem' hresA O hO (zO : Ω') zO.2
    refine ⟨c, ?_⟩
    rw [IsScalarTower.algebraMap_apply K O (ResidueField O), ResidueField.algebraMap_eq, eq_comm,
      ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hmem : (zO : Ω') - algebraMap K Ω' c ∈ O := sub_mem zO.2 (hKO c)
    have h2 := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hc).2
    have hEq : zO - algebraMap K O c = ⟨(zO : Ω') - algebraMap K Ω' c, hmem⟩ := Subtype.ext rfl
    rw [hEq]; exact h2
  let κ : K ≃+* ResidueField O :=
    RingEquiv.ofBijective (algebraMap K (ResidueField O)) ⟨(algebraMap K _).injective, hsurj⟩
  have hκ : ∀ c, κ c = algebraMap K (ResidueField O) c := fun _ => rfl
  refine ⟨κ.symm.toRingHom, fun y => ?_, fun y => ?_⟩
  ·
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    apply κ.injective
    change κ (κ.symm _) = _
    rw [κ.apply_symm_apply, hκ, overRes_residue]

    set c := res (residue W.toValuationSubring a) with hcdef
    rw [IsScalarTower.algebraMap_apply K O (ResidueField O), ResidueField.algebraMap_eq,
      ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hnu : (a : Ω) - algebraMap K Ω c ∈ W.toValuationSubring.nonunits := by
      obtain ⟨c'', hc''⟩ := hresA a a.2

      have hmem'' : (a : Ω) - algebraMap K Ω c'' ∈ W.toValuationSubring := W.toValuationSubring.nonunits_subset hc''
      have hres'' : residue W.toValuationSubring ⟨(a : Ω) - algebraMap K Ω c'', hmem''⟩ = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).2
          (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hc'').2
      have heq : (⟨(a : Ω) - algebraMap K Ω c'', hmem''⟩ : W.toValuationSubring) = a - algebraMap K W.toValuationSubring c'' :=
        Subtype.ext rfl
      rw [heq, map_sub, sub_eq_zero, ← ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply] at hres''
      have hcc : c = c'' := by rw [hcdef, ← ResidueField.algebraMap_eq, hres'', hres]
      rw [hcc]; exact hc''
    have h0 := residue_overHom_eq_zero_of_mem_nonunits (algebraMap Ω Ω') W.toValuationSubring O hO hnu
    rw [IsLocalRing.residue_eq_zero_iff] at h0
    have hEq : overHom (algebraMap Ω Ω') W.toValuationSubring O hO a - algebraMap K O c =
        ⟨algebraMap Ω Ω' ((a : Ω) - algebraMap K Ω c),
          (hO _).2 (W.toValuationSubring.nonunits_subset hnu)⟩ := by
      apply Subtype.ext
      change algebraMap Ω Ω' a - algebraMap K Ω' c = algebraMap Ω Ω' (a - algebraMap K Ω c)
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
    rw [hEq]; exact h0
  ·
    obtain ⟨m, rfl⟩ := IsLocalRing.residue_surjective y
    apply κ.injective
    change κ (κ.symm _) = _
    rw [κ.apply_symm_apply, hκ, overRes_residue]
    set c := e (residue _ m) with hcdef

    have hmc : residue W₀.toValuationSubring m =
        residue W₀.toValuationSubring (algebraMap K W₀.toValuationSubring c) := by
      apply e.injective
      rw [← hcdef, ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply, he]
    have hmax : m - algebraMap K W₀.toValuationSubring c ∈
        IsLocalRing.maximalIdeal W₀.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hmc, sub_self]
    have hmaxO : overHom (ι : M →+* Ω') W₀.toValuationSubring O hι
        (m - algebraMap K W₀.toValuationSubring c) ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax ⊢
      exact fun hu => hmax ((isUnit_map_iff (overHom (ι : M →+* Ω') W₀.toValuationSubring O hι) _).1 hu)
    rw [IsScalarTower.algebraMap_apply K O (ResidueField O), ResidueField.algebraMap_eq,
      ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hEq : overHom (ι : M →+* Ω') W₀.toValuationSubring O hι m - algebraMap K O c =
        overHom (ι : M →+* Ω') W₀.toValuationSubring O hι
          (m - algebraMap K W₀.toValuationSubring c) := by
      apply Subtype.ext
      change (ι : M →+* Ω') m - algebraMap K Ω' c =
        (ι : M →+* Ω') ((m : M) - ((algebraMap K W₀.toValuationSubring c : W₀.toValuationSubring) : M))
      rw [map_sub, Place.coe_algebraMap]
      congr 1
      change algebraMap K Ω' c = ι (algebraMap K M c)
      rw [AlgHom.commutes]
    rw [hEq]; exact hmaxO

end ResidueK

section Read

universe u

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] {N : ℕ} [NeZero N]

theorem isUnit_Δ_of_map_residue_ne_zero {L : Type*} [Field L] {A : ValuationSubring L}
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) : IsUnit W.Δ :=
  (WeierstrassCurve.map_residue_Δ_ne_zero_iff W).1 hΔ

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem read (hN : (N : K) ≠ 0)
    {M : Type u} [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (hcard : Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2)
    (Φ : {H : AddSubgroup ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N} ≃
        {ψ : modularFunctionFieldFullC K N →ₐ[K] M //
          ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap K⟮t⟯ M (WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).j})
    (hΦpin : ∀ (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra M L]
        (H : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
            IsAddCyclic H ∧ Nat.card H = N})
        (d : ℕ) [NeZero d] (hd : d ∣ N)
        (H' : {H' : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
            IsAddCyclic H' ∧ Nat.card H' = d}),
        H'.1 ≤ H.1 →
          algebraMap M L ((Φ H).1 ⟨jqNModC K d, jqModCd_mem_full K N hd⟩) =
            ((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange L).cyclicQuotientJ
              (H'.1.map (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom K⟮t⟯ M L))) d)
    (W₀ : Place K M) [DecidableEq (ResidueField W₀.toValuationSubring)]
    (WA : WeierstrassCurve W₀.toValuationSubring) (κ₀ : VariableChange M)
    (e : ResidueField W₀.toValuationSubring ≃+* K) (γ₀ : VariableChange K)
    (hΔA : (WA.map (residue W₀.toValuationSubring)).Δ ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (θ : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
      →+ E₀.toAffine.Point)
    (h1 : κ₀ • (WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M =
      WA.map W₀.toValuationSubring.subtype)
    (h3 : ∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c)
    (h4 : γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom = E₀)
    (h5 : ∀ (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
        (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point),
        HEq (Point.vcInvFun κ₀ ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine P) P₁ →
        reduceHom hΔA P₁ = 0 → θ P = 0)
    (h6 : ∀ (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
        (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point)
        (x y : ResidueField W₀.toValuationSubring)
        (h : (WA.map (residue W₀.toValuationSubring)).toAffine.Nonsingular x y),
        HEq (Point.vcInvFun κ₀ ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine P) P₁ →
        reduceHom hΔA P₁ = Point.some x y h →
        ∃ h' : E₀.toAffine.Nonsingular (vcXInv γ₀ (e x)) (vcYInv γ₀ (e x) (e y)),
          θ P = Point.some _ _ h')
    (hW₀ : 0 < W₀.ord (t - algebraMap K M E₀.j))
    {x : ModuliPoint N K} (hxj : x.j = E₀.j)
    {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω] (D : ModuliTestDatum K N x Ω) :
    ∃ (P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
      (hP : IsAddCyclic (AddSubgroup.zmultiples P) ∧ Nat.card (AddSubgroup.zmultiples P) = N)
      (hθ : addOrderOf (θ P) = N),
      D.place.toValuationSubring =
        W₀.toValuationSubring.comap
          ((Φ ⟨AddSubgroup.zmultiples P, hP⟩).1 : modularFunctionFieldFullC K N →ₐ[K] M).toRingHom ∧
      x = (Quot.mk _ (⟨E₀, inferInstance, θ P, hθ⟩ : Gamma0Pair N K) : ModuliPoint N K) := by
  have hN0 : N ≠ 0 := NeZero.ne N

  let E : WeierstrassCurve K⟮t⟯ :=
    WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)
  let EM : WeierstrassCurve M := E.baseChange M
  haveI hEell : E.IsElliptic := by
    change (WeierstrassCurve.ofJ _).IsElliptic; infer_instance
  haveI hEMell : EM.IsElliptic := by
    change (E.map (algebraMap K⟮t⟯ M)).IsElliptic; infer_instance
  have hEj : E.j = ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ := WeierstrassCurve.ofJ_j _
  have hEMj : EM.j = t := by
    change (E.map (algebraMap K⟮t⟯ M)).j = t
    rw [WeierstrassCurve.map_j, hEj]; rfl

  letI instκA : DecidableEq (ResidueField D.W.toValuationSubring) := Classical.decEq _
  obtain ⟨hordD, hxD⟩ := D.reduction

  set j₁ : Ω := D.emb (jModElt K (jqModC_mem_full K N)) with hj₁def
  have hj₁E : j₁ = (D.curve.map D.W.toValuationSubring.subtype).j := by
    rw [hj₁def, ← jqNFull_one K N, D.emb_jqNFull_one]
  have hj₁tr : Transcendental K j₁ := by
    have h0 : Transcendental K (jModElt K (jqModC_mem_full K N) : modularFunctionFieldFullC K N) := by
      intro halg
      apply ModularCurve.transcendental_jqModC K
      exact halg.algebraMap (A := LaurentSeries K)
    intro halg
    exact h0 ((isAlgebraic_algHom_iff D.emb D.emb.toRingHom.injective).1 halg)
  have hj₁W : j₁ - algebraMap K Ω E₀.j ∈ D.W.toValuationSubring.nonunits := by
    have h := D.ord_emb_jModElt_sub_pos
    rw [map_sub, AlgHom.commutes, hxj] at h
    exact mem_nonunits_of_ord_pos D.W h
  have hW₀' : t - algebraMap K M E₀.j ∈ W₀.toValuationSubring.nonunits :=
    mem_nonunits_of_ord_pos W₀ hW₀

  let Ω' : Type u := AlgebraicClosure Ω
  letI instΩ' : DecidableEq Ω' := Classical.decEq _
  obtain ⟨O, ι, hO, hιt, hιO⟩ :=
    AlgebraicCurve.Place.exists_valuationSubring_algHom_apply_eq_forall_mem_iff t ht W₀ E₀.j hW₀'
      D.W j₁ hj₁tr hj₁W Ω'
  letI instκO : DecidableEq (ResidueField O) := Classical.decEq _
  let ιr : M →+* Ω' := (ι : M →+* Ω')
  have hιr : ∀ m, ιr m = ι m := fun _ => rfl
  have hιO' : ∀ m, ιr m ∈ O ↔ m ∈ W₀.toValuationSubring := hιO
  letI algMΩ' : Algebra M Ω' := ιr.toAlgebra
  let ιₐ : M →ₐ[K⟮t⟯] Ω' := IsScalarTower.toAlgHom K⟮t⟯ M Ω'
  have hιₐ : ∀ m, ιₐ m = ι m := fun _ => rfl
  have hιₐr : (ιₐ : M →+* Ω') = ιr := RingHom.ext fun _ => rfl

  have hNM : (N : M) ≠ 0 := by
    rw [← map_natCast (algebraMap K M)]; exact (_root_.map_ne_zero _).mpr hN
  have hNΩ' : (N : Ω') ≠ 0 := by
    rw [← map_natCast ιr]; exact (_root_.map_ne_zero _).mpr hNM

  let ιO : W₀.toValuationSubring →+* O := overHom ιr W₀.toValuationSubring O hιO'
  let aO : D.W.toValuationSubring →+* O := overHom (algebraMap Ω Ω') D.W.toValuationSubring O hO
  let ιk : ResidueField W₀.toValuationSubring →+* ResidueField O := overRes ιr W₀.toValuationSubring O hιO'
  let ak : ResidueField D.W.toValuationSubring →+* ResidueField O :=
    overRes (algebraMap Ω Ω') D.W.toValuationSubring O hO
  haveI hWAell : WA.IsElliptic := ⟨isUnit_Δ_of_map_residue_ne_zero hΔA⟩
  let WA' : WeierstrassCurve O := WA.map ιO
  let 𝓔' : WeierstrassCurve O := D.curve.map aO
  haveI hWA'ell : WA'.IsElliptic := by change (WA.map ιO).IsElliptic; infer_instance
  haveI h𝓔'ell : 𝓔'.IsElliptic := by change (D.curve.map aO).IsElliptic; infer_instance
  have F1A : (WA.map W₀.toValuationSubring.subtype).map ιr = WA'.map O.subtype :=
    map_overHom_map_subtype ιr W₀.toValuationSubring O hιO' WA
  have F1D : (D.curve.map D.W.toValuationSubring.subtype).map (algebraMap Ω Ω') = 𝓔'.map O.subtype :=
    map_overHom_map_subtype (algebraMap Ω Ω') D.W.toValuationSubring O hO D.curve
  have F2A : (WA.map (residue W₀.toValuationSubring)).map ιk = WA'.map (residue O) :=
    map_overHom_map_residue ιr W₀.toValuationSubring O hιO' WA
  have F2D : (D.curve.map (residue D.W.toValuationSubring)).map ak = 𝓔'.map (residue O) :=
    map_overHom_map_residue (algebraMap Ω Ω') D.W.toValuationSubring O hO D.curve
  have hΔA' : (WA'.map (residue O)).Δ ≠ 0 := by
    rw [← F2A, WeierstrassCurve.map_Δ]
    exact (map_ne_zero_iff _ (RingHom.injective _)).2 hΔA
  have hΔD' : (𝓔'.map (residue O)).Δ ≠ 0 := by
    rw [← F2D, WeierstrassCurve.map_Δ]
    exact (map_ne_zero_iff _ (RingHom.injective _)).2 D.map_Δ_ne_zero
  have F4 : (WA.map W₀.toValuationSubring.subtype).map ιr = (κ₀.map ιr) • (EM.map ιr) := by
    rw [← h1]; exact (WeierstrassCurve.map_variableChange EM κ₀ ιr).symm
  have hcΩ : EM.map ιr = E.baseChange Ω' := by
    rw [← hιₐr]; exact WeierstrassCurve.map_baseChange E ιₐ

  have jcongr : ∀ {V V' : WeierstrassCurve Ω'} [V.IsElliptic] [V'.IsElliptic],
      V = V' → V.j = V'.j := by
    intro V V' _ _ hVV'; subst hVV'; rfl
  have hjD : (𝓔'.map O.subtype).j = algebraMap Ω Ω' j₁ := by
    rw [jcongr F1D.symm, WeierstrassCurve.map_j, ← hj₁E]
  have hjA : (WA'.map O.subtype).j = algebraMap Ω Ω' j₁ := by
    rw [jcongr (F1A.symm.trans F4), WeierstrassCurve.variableChange_j, WeierstrassCurve.map_j, hEMj,
      hιr, hιt]
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ (hjD.trans hjA.symm)
  obtain ⟨C₀, hC₀W, hC₀, hred₀, hpts⟩ :=
    WeierstrassCurve.exists_variableChange_map_eq_and_reduceHom_vcFun_eq (A := O) hΔD' hΔA' C hC

  set g' : (𝓔'.map O.subtype).toAffine.Point := mapPt (algebraMap Ω Ω') F1D D.gen with hg'def
  have hg'ord : addOrderOf g' = N := by
    rw [hg'def, addOrderOf_injective (mapPt _ F1D) (mapPt_injective _ F1D), D.addOrderOf_gen]
  set Q : (C • 𝓔'.map O.subtype).toAffine.Point :=
    Point.vcInvFun C (𝓔'.map O.subtype).toAffine g' with hQdef
  have hgQ : Point.vcFun C (𝓔'.map O.subtype).toAffine Q = g' := Point.vcFun_rightInverse g'
  have hQord : addOrderOf Q = N := by rw [hQdef, addOrderOf_vcInvFun, hg'ord]
  set Q₂ : (WA'.map O.subtype).toAffine.Point := castHom hC Q with hQ₂def
  have hQ₂ord : addOrderOf Q₂ = N := by rw [hQ₂def, addOrderOf_castHom, hQord]

  have hcardA : Nat.card {P : (WA.map W₀.toValuationSubring.subtype).toAffine.Point // N • P = 0} =
      N ^ 2 := by
    rw [← hcard]
    symm
    refine Nat.card_congr ?_
    let eqv : EM.toAffine.Point ≃ (WA.map W₀.toValuationSubring.subtype).toAffine.Point :=
      { toFun := fun P => castHom h1 (Point.vcInvFun κ₀ EM.toAffine P)
        invFun := fun P₁ => Point.vcFun κ₀ EM.toAffine (castHom h1.symm P₁)
        left_inv := fun P => by
          simp only [castHom_symm_castHom]; exact Point.vcFun_rightInverse P
        right_inv := fun P₁ => by
          simp only [Point.vcFun_leftInverse _]; exact castHom_castHom_symm h1 P₁ }
    refine eqv.subtypeEquiv fun P => ?_
    change N • P = 0 ↔ N • ((castHom h1).comp (vcInvHom κ₀ EM.toAffine)) P = 0
    rw [← map_nsmul]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0
      have hinj : Function.Injective ((castHom h1).comp (vcInvHom κ₀ EM.toAffine)) :=
        (castHom_injective h1).comp (vcInvFun_injective κ₀ EM.toAffine)
      exact hinj (by rw [h0, map_zero])
  obtain ⟨P₁, hP₁N, hP₁⟩ := exists_mapPoint_eq_of_nsmul_eq_zero ιr (WA.map W₀.toValuationSubring.subtype)
    hNΩ' hcardA (castHom F1A.symm Q₂)
    (by rw [← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_castHom, hQ₂ord])
  have hP₁Q₂ : mapPt ιr F1A P₁ = Q₂ := by
    rw [mapPt_apply, hP₁, castHom_castHom_symm]
  have hP₁ord : addOrderOf P₁ = N := by
    rw [← hQ₂ord, ← hP₁Q₂, addOrderOf_injective (mapPt ιr F1A) (mapPt_injective ιr F1A)]
  set P : EM.toAffine.Point := Point.vcFun κ₀ EM.toAffine (castHom h1.symm P₁) with hPdef
  have hPinv : Point.vcInvFun κ₀ EM.toAffine P = castHom h1.symm P₁ := by
    rw [hPdef]; exact Point.vcFun_leftInverse _
  have hHEq : HEq (Point.vcInvFun κ₀ EM.toAffine P) P₁ := by
    rw [hPinv]; exact heq_castHom h1.symm P₁
  have hPord : addOrderOf P = N := by
    rw [hPdef, addOrderOf_vcFun, addOrderOf_castHom, hP₁ord]
  have hNP : N • P = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (hPord ▸ dvd_rfl)

  set Rr : (WA'.map (residue O)).toAffine.Point := reduceHom hΔA' Q₂ with hRrdef
  set R : ((C₀.map (residue O)) • 𝓔'.map (residue O)).toAffine.Point := castHom hred₀.symm Rr
    with hRdef
  have hRRr : HEq R Rr := heq_castHom hred₀.symm Rr
  have hred_g' : reduceHom hΔD' g' =
      Point.vcFun (C₀.map (residue O)) (𝓔'.map (residue O)).toAffine R := by
    rw [← hgQ]
    exact hpts Q Q₂ (heq_castHom hC Q).symm R hRRr
  obtain ⟨R_A, hR_Adef⟩ :
      ∃ R_A : (WA.map (residue W₀.toValuationSubring)).toAffine.Point, R_A = reduceHom hΔA P₁ :=
    ⟨_, rfl⟩
  have hRr : Rr = mapPt ιk F2A R_A := by
    rw [hRrdef, ← hP₁Q₂, hR_Adef]
    exact reduceHom_mapPt ιr W₀.toValuationSubring O hιO' WA hΔA hΔA' P₁
  obtain ⟨R_D, hR_Ddef⟩ :
      ∃ R_D : (D.curve.map (residue D.W.toValuationSubring)).toAffine.Point,
        R_D = reduceHom D.map_Δ_ne_zero D.gen :=
    ⟨_, rfl⟩
  have hg'red : reduceHom hΔD' g' = mapPt ak F2D R_D := by
    rw [hg'def, hR_Ddef]
    exact reduceHom_mapPt (algebraMap Ω Ω') D.W.toValuationSubring O hO D.curve D.map_Δ_ne_zero
      hΔD' D.gen

  have hR_Dord : addOrderOf R_D = N := by rw [hR_Ddef]; exact hordD
  have hg'redord : addOrderOf (reduceHom hΔD' g') = N := by
    rw [hg'red, addOrderOf_injective (mapPt ak F2D) (mapPt_injective _ _), hR_Dord]
  have hRord : addOrderOf R = N := by
    rw [← hg'redord, hred_g', addOrderOf_vcFun]
  have hRrord : addOrderOf Rr = N := by rw [← hRord, hRdef, addOrderOf_castHom]
  have hR_Aord : addOrderOf R_A = N := by
    rw [← hRrord, hRr, addOrderOf_injective (mapPt ιk F2A) (mapPt_injective ιk F2A)]

  set WAe : WeierstrassCurve K := (WA.map (residue W₀.toValuationSubring)).map e.toRingHom
    with hWAedef
  have hWAe : (WA.map (residue W₀.toValuationSubring)).map e.toRingHom = WAe := rfl
  set gen_e : WAe.toAffine.Point := mapPt e.toRingHom hWAe R_A with hgen_edef
  have hgen_eord : addOrderOf gen_e = N := by
    rw [hgen_edef, addOrderOf_injective (mapPt e.toRingHom hWAe) (mapPt_injective _ _), hR_Aord]

  have hθP : θ P = castHom h4 (Point.vcInvFun γ₀ WAe.toAffine gen_e) := by
    rw [hgen_edef]
    rcases R_A with _ | ⟨xx, yy, hxy⟩
    · have h0 : θ P = 0 := h5 P P₁ hHEq (by rw [← hR_Adef]; rfl)
      rw [h0, ← WeierstrassCurve.Affine.Point.zero_def, map_zero, Point.vcInvFun_zero, map_zero]
    · obtain ⟨h', hθ'⟩ := h6 P P₁ xx yy hxy hHEq hR_Adef.symm
      rw [hθ', mapPt_some]
      change _ = castHom h4 (Point.some (vcXInv γ₀ (e xx)) (vcYInv γ₀ (e xx) (e yy)) _)
      rw [castHom_some]
  have hθord : addOrderOf (θ P) = N := by
    rw [hθP, addOrderOf_castHom, addOrderOf_vcInvFun, hgen_eord]

  have hcast : ∀ T : EM.toAffine.Point,
      castHom hcΩ (WeierstrassCurve.mapPoint ιr (W₀ := EM) T) =
        WeierstrassCurve.Affine.Point.map (W' := E) ιₐ T := by
    intro T
    cases T with
    | zero => exact (map_zero (castHom hcΩ)).trans (map_zero _).symm
    | some x' y' h => rw [WeierstrassCurve.mapPoint_some, castHom_some]; rfl
  have hchain : ∀ (n d : ℕ), (d : Ω') ≠ 0 →
      ((D.curve.map D.W.toValuationSubring.subtype).map (algebraMap Ω Ω')).cyclicQuotientJ
          (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap Ω Ω') ((n : ℕ) • D.gen))) d =
        (E.baseChange Ω').cyclicQuotientJ
          (AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.map (W' := E) ιₐ (n • P))) d := by
    intro n d hd
    have e1 : WeierstrassCurve.mapPoint (algebraMap Ω Ω') (n • D.gen) = castHom F1D.symm (n • g') := by
      rw [hg'def, map_nsmul, mapPt_apply, castHom_symm_castHom, WeierstrassCurve.mapPoint_nsmul]
    have h3 : castHom (hC.trans (F1A.symm.trans F4)) Q = castHom F4 (castHom F1A.symm Q₂) := by
      rw [hQ₂def]
      have key : ∀ {V₁ V₂ V₃ V₄ : WeierstrassCurve Ω'} (h12 : V₁ = V₂) (h23 : V₂ = V₃)
          (h34 : V₃ = V₄) (T : V₁.toAffine.Point),
          castHom (h12.trans (h23.trans h34)) T = castHom h34 (castHom h23 (castHom h12 T)) := by
        intro V₁ V₂ V₃ V₄ h12 h23 h34 T; subst h12; subst h23; subst h34; rfl
      exact key hC F1A.symm F4 Q
    have hkey : Point.vcFun (κ₀.map ιr) (EM.map ιr).toAffine (castHom (hC.trans (F1A.symm.trans F4)) Q) =
        WeierstrassCurve.mapPoint ιr (W₀ := EM) P := by
      apply vcInvFun_injective (κ₀.map ιr) (EM.map ιr).toAffine
      rw [Point.vcFun_leftInverse]
      have hsq := ModularCurve.mapPoint_vcInvFun_heq ιr κ₀ EM P
      rw [hPinv] at hsq
      have h2 : HEq (WeierstrassCurve.mapPoint ιr (W₀ := κ₀ • EM) (castHom h1.symm P₁))
          (WeierstrassCurve.mapPoint ιr (W₀ := WA.map W₀.toValuationSubring.subtype) P₁) :=
        heq_mapPoint_castHom ιr h1.symm P₁
      rw [hP₁] at h2
      rw [h3]
      have h3' : HEq (castHom F4 (castHom F1A.symm Q₂)) (castHom F1A.symm Q₂) := heq_castHom F4 _
      exact eq_of_heq (h3'.trans (h2.symm.trans hsq))
    calc ((D.curve.map D.W.toValuationSubring.subtype).map (algebraMap Ω Ω')).cyclicQuotientJ
          (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap Ω Ω') (n • D.gen))) d
        = (𝓔'.map O.subtype).cyclicQuotientJ (AddSubgroup.zmultiples (n • g')) d := by
          rw [e1, ← cyclicQuotientJ_map_castHom F1D.symm (AddSubgroup.zmultiples (n • g')) d,
            AddMonoidHom.map_zmultiples]
      _ = (C • 𝓔'.map O.subtype).cyclicQuotientJ (AddSubgroup.zmultiples (n • Q)) d := by
          rw [cyclicQuotientJ_smul_zmultiples hd C, vcFun_nsmul, hgQ]
      _ = ((κ₀.map ιr) • (EM.map ιr)).cyclicQuotientJ
            (AddSubgroup.zmultiples (castHom (hC.trans (F1A.symm.trans F4)) (n • Q))) d := by
          rw [← cyclicQuotientJ_map_castHom (hC.trans (F1A.symm.trans F4)) _ d,
            AddMonoidHom.map_zmultiples]
      _ = (EM.map ιr).cyclicQuotientJ
            (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint ιr (W₀ := EM) (n • P))) d := by
          rw [cyclicQuotientJ_smul_zmultiples hd, map_nsmul (castHom (hC.trans (F1A.symm.trans F4))),
            vcFun_nsmul, hkey, WeierstrassCurve.mapPoint_nsmul]
      _ = (E.baseChange Ω').cyclicQuotientJ
            (AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.map (W' := E) ιₐ (n • P))) d := by
          rw [← cyclicQuotientJ_map_castHom hcΩ, AddMonoidHom.map_zmultiples, hcast]

  have hHP : IsAddCyclic (AddSubgroup.zmultiples P) ∧ Nat.card (AddSubgroup.zmultiples P) = N :=
    ⟨AddSubgroup.isAddCyclic_zmultiples P, (Nat.card_zmultiples P).trans hPord⟩
  set H : {H : AddSubgroup EM.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
    ⟨AddSubgroup.zmultiples P, hHP⟩ with hHdef
  have hagree : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
      algebraMap Ω Ω' (D.emb (jqNFull K N d hd)) = ι ((Φ H).1 (jqNFull K N d hd)) := by
    intro d _ hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hq : 0 < N / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd) hd0
    have hdΩ' : (d : Ω') ≠ 0 := by
      obtain ⟨c, hc⟩ := hd
      intro h0
      apply hNΩ'
      rw [hc, Nat.cast_mul, h0, zero_mul]
    have hd' : addOrderOf ((N / d) • P) = d := by
      rw [addOrderOf_nsmul' _ hq.ne', hPord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
        Nat.div_div_self hd hN0]
    let H' : {H' : AddSubgroup EM.toAffine.Point // IsAddCyclic H' ∧ Nat.card H' = d} :=
      ⟨AddSubgroup.zmultiples ((N / d) • P), AddSubgroup.isAddCyclic_zmultiples _,
        (Nat.card_zmultiples _).trans hd'⟩
    have hle : H'.1 ≤ H.1 :=
      AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples P) _)
    have hv := hΦpin Ω' H d hd H' hle
    have hDpin := D.emb_jqNFull Ω' d hd
    rw [hDpin, hchain (N / d) d hdΩ']
    change _ = algebraMap M Ω' ((Φ H).1 ⟨jqNModC K d, jqModCd_mem_full K N hd⟩)
    rw [hv, AddMonoidHom.map_zmultiples]
  have hfun : (IsScalarTower.toAlgHom K Ω Ω').comp D.emb = ι.comp ((Φ H).1) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (F := K) (E := LaurentSeries K)
      (S := modularFunctionFieldFullC K N) (s := divisorExpansionsC K N) rfl ?_
    rintro y ⟨d, hd0, hd, rfl⟩
    haveI := hd0
    exact hagree d hd

  have hplace : D.place.toValuationSubring =
      W₀.toValuationSubring.comap ((Φ H).1 : modularFunctionFieldFullC K N →ₐ[K] M).toRingHom := by
    ext f
    rw [ModuliTestDatum.place_toValuationSubring, ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    change D.emb f ∈ D.W.toValuationSubring ↔ (Φ H).1 f ∈ W₀.toValuationSubring
    rw [← hO, ← hιO]
    have hf := congrArg (fun φ : modularFunctionFieldFullC K N →ₐ[K] Ω' => φ f) hfun
    change algebraMap Ω Ω' (D.emb f) = ι ((Φ H).1 f) at hf
    rw [hf]

  obtain ⟨ē, hēa, hēι⟩ := exists_ringHom_residueField (K := K) D.W D.res D.res_algebraMap O hO W₀ ι
    hιO' e h3
  have hres_comp : D.res = ē.comp ak := RingHom.ext fun y => (hēa y).symm
  have he_comp : ē.comp ιk = e.toRingHom := RingHom.ext fun y => hēι y
  have hclass : x = (Quot.mk _ (⟨E₀, inferInstance, θ P, hθord⟩ : Gamma0Pair N K) : ModuliPoint N K) := by
    rw [← hxD, hres_comp, ModuliPoint.map_comp, ModuliPoint.map_mk]

    have stepA : Gamma0Pair.map ak
          (⟨D.curve.map (residue D.W.toValuationSubring), ⟨isUnit_iff_ne_zero.mpr D.map_Δ_ne_zero⟩,
            reduceHom D.map_Δ_ne_zero D.gen, hordD⟩ :
            Gamma0Pair N (ResidueField D.W.toValuationSubring)) =
        (⟨𝓔'.map (residue O), ⟨isUnit_iff_ne_zero.mpr hΔD'⟩, reduceHom hΔD' g', hg'redord⟩ :
          Gamma0Pair N (ResidueField O)) := by
      refine gamma0Pair_eq F2D ?_
      change HEq (WeierstrassCurve.mapPoint ak (reduceHom D.map_Δ_ne_zero D.gen)) (reduceHom hΔD' g')
      rw [hg'red, ← hR_Ddef, mapPt_apply]
      exact (heq_castHom F2D _).symm
    rw [stepA]

    have stepB : (Quot.mk _ (⟨𝓔'.map (residue O), ⟨isUnit_iff_ne_zero.mpr hΔD'⟩, reduceHom hΔD' g',
          hg'redord⟩ : Gamma0Pair N (ResidueField O)) : ModuliPoint N (ResidueField O)) =
        Quot.mk _ (⟨WA'.map (residue O), ⟨isUnit_iff_ne_zero.mpr hΔA'⟩, Rr, hRrord⟩ :
          Gamma0Pair N (ResidueField O)) := by
      refine Quot.sound ⟨C₀.map (residue O), hred₀, 1, Nat.coprime_one_left N, ?_⟩
      change HEq Rr ((1 : ℕ) • Point.vcInvFun (C₀.map (residue O)) (𝓔'.map (residue O)).toAffine
        (reduceHom hΔD' g'))
      rw [one_nsmul, hred_g', Point.vcFun_leftInverse]
      exact hRRr.symm
    rw [stepB]

    have stepC : Gamma0Pair.map ιk
          (⟨WA.map (residue W₀.toValuationSubring), ⟨isUnit_iff_ne_zero.mpr hΔA⟩, R_A, hR_Aord⟩ :
            Gamma0Pair N (ResidueField W₀.toValuationSubring)) =
        (⟨WA'.map (residue O), ⟨isUnit_iff_ne_zero.mpr hΔA'⟩, Rr, hRrord⟩ :
          Gamma0Pair N (ResidueField O)) := by
      refine gamma0Pair_eq F2A ?_
      change HEq (WeierstrassCurve.mapPoint ιk R_A) Rr
      rw [hRr, mapPt_apply]
      exact (heq_castHom F2A _).symm
    rw [← stepC, ← ModuliPoint.map_mk, ← ModuliPoint.map_comp, he_comp, ModuliPoint.map_mk]

    have stepD : Gamma0Pair.map e.toRingHom
          (⟨WA.map (residue W₀.toValuationSubring), ⟨isUnit_iff_ne_zero.mpr hΔA⟩, R_A, hR_Aord⟩ :
            Gamma0Pair N (ResidueField W₀.toValuationSubring)) =
        (⟨WAe, inferInstance, gen_e, hgen_eord⟩ : Gamma0Pair N K) := by
      refine gamma0Pair_eq hWAe ?_
      change HEq (WeierstrassCurve.mapPoint e.toRingHom R_A) gen_e
      rw [hgen_edef, mapPt_apply]
      exact (heq_castHom hWAe _).symm
    rw [stepD]

    refine Quot.sound ⟨γ₀, h4, 1, Nat.coprime_one_left N, ?_⟩
    change HEq (θ P) ((1 : ℕ) • Point.vcInvFun γ₀ WAe.toAffine gen_e)
    rw [one_nsmul, hθP]
    exact heq_castHom h4 _
  exact ⟨P, hHP, hθord, hplace, hclass⟩

end Read

section Unique

universe u

set_option maxHeartbeats 16000000 in

theorem eq_of_isModuliPlaceOf (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] (N : ℕ)
    [NeZero N] (hN : (N : K) ≠ 0) (x : ModuliPoint N K)
    (v v' : Place K (modularFunctionFieldFullC K N))
    (h : IsModuliPlaceOf K N x v) (h' : IsModuliPlaceOf K N x v') : v = v' := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hN0 : N ≠ 0 := NeZero.ne N
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, rfl⟩
    apply hN
    rw [Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul]

  obtain ⟨A₀, rfl⟩ := Quot.exists_rep x
  obtain ⟨E₀, hE₀, g₀, hg₀⟩ := A₀

  obtain ⟨M, iF, iD, iA, t, htr, hfd, hgal, hcard, hall⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom K p N hN
  haveI : Algebra.IsSeparable K⟮t⟯ M := IsGalois.to_isSeparable
  obtain ⟨W₀, hW₀⟩ := exists_place_ord_pos K t htr E₀.j
  letI := Classical.decEq (ResidueField W₀.toValuationSubring)
  obtain ⟨WA, κ₀, e, γ₀, hΔA, θ, ρ, h1, -, h3, h4, h5, h6, hθinj, -, -, -, hreal, -⟩ :=
    hall E₀.j E₀ rfl W₀ hW₀

  have hjt : Transcendental K (WeierstrassCurve.ofJ
      (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).j := by
    rw [WeierstrassCurve.ofJ_j]
    exact (transcendental_algebraMap_iff (R := K) (A := M)
      (algebraMap K⟮t⟯ M).injective).mp htr
  obtain ⟨Φ, hΦnat, hΦpin⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
      K N hN K⟮t⟯ M (WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)) hjt hcard

  obtain ⟨Ω₁, _, _, _, D₁, hD₁⟩ := h
  obtain ⟨Ω₂, _, _, _, D₂, hD₂⟩ := h'
  have hxj : ModuliPoint.j (Quot.mk _ (⟨E₀, hE₀, g₀, hg₀⟩ : Gamma0Pair N K) : ModuliPoint N K) = E₀.j :=
    rfl
  obtain ⟨P₁, hH₁, hθ₁, hpl₁, hcls₁⟩ := read hN t htr hcard Φ
    (fun L _ _ _ _ H d _ hd H' hle => hΦpin L H d hd H' hle)
    W₀ WA κ₀ e γ₀ hΔA E₀ θ h1 h3 h4 h5 h6 hW₀ hxj D₁
  obtain ⟨P₂, hH₂, hθ₂, hpl₂, hcls₂⟩ := read hN t htr hcard Φ
    (fun L _ _ _ _ H d _ hd H' hle => hΦpin L H d hd H' hle)
    W₀ WA κ₀ e γ₀ hΔA E₀ θ h1 h3 h4 h5 h6 hW₀ hxj D₂

  obtain ⟨γ, hγ, k, hk, hgen⟩ :=
    (ModularCurve.ModuliPoint.mk_eq_mk_iff_step _ _).1 (hcls₁.symm.trans hcls₂)
  change γ • E₀ = E₀ at hγ
  change HEq (θ P₂) (k • Point.vcInvFun γ E₀.toAffine (θ P₁)) at hgen

  obtain ⟨σ, hσ, hε⟩ := hreal γ hγ
  set σP₁ := WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P₁ with hσP₁
  have hNP₁ : N • P₁ = 0 := by
    have hord : addOrderOf P₁ = N := (Nat.card_zmultiples P₁).symm.trans hH₁.2
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hord ▸ dvd_rfl)
  have hNP₂ : N • P₂ = 0 := by
    have hord : addOrderOf P₂ = N := (Nat.card_zmultiples P₂).symm.trans hH₂.2
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hord ▸ dvd_rfl)
  have hNσP₁ : N • σP₁ = 0 := by rw [hσP₁, ← map_nsmul, hNP₁, map_zero]
  have hNθ : N • θ σP₁ = 0 := by rw [← map_nsmul, hNσP₁, map_zero]
  have hE₀eq : (γ • E₀.toAffine).toAffine = E₀.toAffine := congrArg WeierstrassCurve.toAffine hγ
  have hz2 : AddSubgroup.zmultiples (θ P₂) = AddSubgroup.zmultiples (θ σP₁) := by
    rcases hε with hε | hε
    · have hh : HEq (k • Point.vcInvFun γ E₀.toAffine (θ P₁)) (k • θ σP₁) :=
        ModularCurve.Point.heq_nsmul hE₀eq k (hε P₁)
      have heq : θ P₂ = k • θ σP₁ := eq_of_heq (hgen.trans hh)
      rw [heq]
      exact zmultiples_nsmul_eq_of_coprime hNθ hk
    · have hh : HEq (k • Point.vcInvFun γ E₀.toAffine (θ P₁)) (k • -θ σP₁) :=
        ModularCurve.Point.heq_nsmul hE₀eq k (hε P₁)
      have heq : θ P₂ = k • -θ σP₁ := eq_of_heq (hgen.trans hh)
      rw [heq, zmultiples_nsmul_eq_of_coprime (by rw [smul_neg, hNθ, neg_zero]) hk,
        AddSubgroup.zmultiples_neg]

  have hθinj' : ∀ Q, N • Q = 0 → θ Q = 0 → Q = 0 := fun Q hQ h0 => hθinj N Q hpN hQ h0
  have hz3 : AddSubgroup.zmultiples P₂ = AddSubgroup.zmultiples σP₁ :=
    zmultiples_eq_of_map_eq θ hθinj' hNP₂ hNσP₁ hz2
  have hz4 : (⟨AddSubgroup.zmultiples P₂, hH₂⟩ : {H : AddSubgroup ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}).1 =
      (⟨AddSubgroup.zmultiples P₁, hH₁⟩ : {H : AddSubgroup ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}).1.map
        (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)) := by
    change AddSubgroup.zmultiples P₂ = (AddSubgroup.zmultiples P₁).map _
    rw [AddMonoidHom.map_zmultiples, hz3]
  have hΦσ := hΦnat σ ⟨_, hH₁⟩ ⟨_, hH₂⟩ hz4

  apply Place.ext
  rw [hD₁, hD₂]
  change D₁.place.toValuationSubring = D₂.place.toValuationSubring
  rw [hpl₁, hpl₂]
  ext f
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, hΦσ]
  change _ ↔ σ ((Φ ⟨_, hH₁⟩).1 f) ∈ W₀.toValuationSubring
  exact (mem_iff_of_smul_eq hσ _).symm

end Unique

end ModuliPlaceUnique
p2m_reactivate "P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt.ModularCurve.ModuliPlaceUnique"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt.ModularCurve.ModuliPlaceUnique P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt.ModularCurve.ModuliPlaceUnique P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt.ModularCurve"

set_option linter.unusedVariables false in
universe u in
theorem solution
    (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (x : ModularCurve.ModuliPoint N K) (v v' : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldFullC K N))
    (h : ModularCurve.IsModuliPlaceOf K N x v) (h' : ModularCurve.IsModuliPlaceOf K N x v')
    (a : ↥(ModularCurve.modularFunctionFieldFullC K N)) (ha : (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0)) :
    a ∈ v.toValuationSubring.nonunits ↔ a ∈ v'.toValuationSubring.nonunits := by
  rw [ModularCurve.ModuliPlaceUnique.eq_of_isModuliPlaceOf K N hN x v v' h h']

end S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt
end P2MW
export P2MW.S_ModularCurve_IsModuliPlaceOf_mem_nonunits_iff_of_isIntegral_jModElt (solution)
