-- Prove2me | solution 1 for ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d38beff1-3c72-53cf-95e3-612f0e37325a

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ
import Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples
import Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_j_tateLaurent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"

set_option autoImplicit false

open ModularCurve WeierstrassCurve

namespace P2MKcCH1AllD

theorem map_cyclic_card {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (H : AddSubgroup A) {n : ℕ}
    (hH : IsAddCyclic H ∧ Nat.card H = n) :
    IsAddCyclic (H.map f) ∧ Nat.card (H.map f) = n := by
  obtain ⟨hc, hcard⟩ := hH
  let e := H.equivMapOfInjective f hf
  exact ⟨isAddCyclic_of_surjective e e.surjective,
    by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm⟩

theorem comap_cyclic_card {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (H' : AddSubgroup B) (hle : H' ≤ f.range) {n : ℕ}
    (hH' : IsAddCyclic H' ∧ Nat.card H' = n) :
    (H'.comap f).map f = H' ∧ IsAddCyclic (H'.comap f) ∧ Nat.card (H'.comap f) = n := by
  obtain ⟨hc, hcard⟩ := hH'
  have hmap : (H'.comap f).map f = H' := by
    rw [AddSubgroup.map_comap_eq, inf_eq_right.2 hle]
  let e := (H'.comap f).equivMapOfInjective f hf
  have e' : (H'.comap f) ≃+ H' := e.trans (AddEquiv.addSubgroupCongr hmap)
  exact ⟨hmap, isAddCyclic_of_surjective e'.symm e'.symm.surjective,
    by rw [← hcard]; exact Nat.card_congr e'.toEquiv⟩

theorem nsmul_eq_zero_of_mem {A : Type*} [AddCommGroup A] {H : AddSubgroup A} {N : ℕ}
    (hH : Nat.card H = N) {P : A} (hP : P ∈ H) : N • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH] at this
  exact congrArg Subtype.val this

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k M : Type*} [Field k] [Field M] [Algebra k M]
    [IsAlgClosed M] [DecidableEq M] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : M) ≠ 0) :
    Nat.card {Q : (E.baseChange M).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := M) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem torsion_mem_range {F A B : Type*} [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]
    [IsAlgClosed A] [DecidableEq A] [IsAlgClosed B] [DecidableEq B]
    (E : WeierstrassCurve F) [E.IsElliptic] (f : A →ₐ[F] B) (N : ℕ) [NeZero N]
    (hNA : (N : A) ≠ 0) (hNB : (N : B) ≠ 0)
    (Q : (E.baseChange B).toAffine.Point) (hQ : N • Q = 0) :
    Q ∈ (WeierstrassCurve.Affine.Point.map f :
      (E.baseChange A).toAffine.Point →+ (E.baseChange B).toAffine.Point).range := by
  obtain ⟨P, -, hP⟩ := exists_eq_of_nsmul_eq_zero (WeierstrassCurve.Affine.Point.map f)
    (WeierstrassCurve.Affine.Point.map_injective f) N
    (natCard_torsion_of_isAlgClosed (M := A) E N hNA) (natCard_torsion_of_isAlgClosed (M := B) E N hNB)
    Q hQ
  exact ⟨P, hP⟩

theorem exists_addEquiv_variableChange {L : Type*} [Field L] [DecidableEq L]
    (E T : WeierstrassCurve L) (C : VariableChange L) (h : C • E = T) :
    ∃ g : E.toAffine.Point ≃+ T.toAffine.Point,
      ∀ (H : AddSubgroup E.toAffine.Point) (n : ℕ), (n : L) ≠ 0 →
        T.cyclicQuotientJ (H.map g.toAddMonoidHom) n = E.cyclicQuotientJ H n := by
  subst h
  let g : E.toAffine.Point ≃+ (C • E).toAffine.Point :=
    { toFun := WeierstrassCurve.Affine.Point.vcInvFun C E.toAffine
      invFun := WeierstrassCurve.Affine.Point.vcFun C E.toAffine
      left_inv := WeierstrassCurve.Affine.Point.vcFun_rightInverse
      right_inv := WeierstrassCurve.Affine.Point.vcFun_leftInverse
      map_add' := WeierstrassCurve.Affine.Point.vcInvFun_add C E.toAffine }
  refine ⟨g, fun H n hn => ?_⟩
  refine WeierstrassCurve.cyclicQuotientJ_variableChange_eq C E H (H.map g.toAddMonoidHom) ?_ n hn
  intro P
  rw [AddSubgroup.mem_map_equiv]
  rfl

universe u v

theorem tate_witness (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (M₁ : Type v) [Field M₁] [DecidableEq M₁] [IsAlgClosed M₁]
    [Algebra (modularFunctionFieldFullC K N) M₁]
    [Algebra.IsAlgebraic (modularFunctionFieldFullC K N) M₁]
    (E₁ : WeierstrassCurve (modularFunctionFieldFullC K N)) [E₁.IsElliptic]
    (hj : E₁.j = ⟨jqModC K, jqModC_mem_full K N⟩) :
    ∃ H₁ : AddSubgroup (E₁.baseChange M₁).toAffine.Point, (IsAddCyclic H₁ ∧ Nat.card H₁ = N) ∧
      ∀ (d : ℕ) [NeZero d] (hd : d ∣ N) (H₁' : AddSubgroup (E₁.baseChange M₁).toAffine.Point),
        IsAddCyclic H₁' ∧ Nat.card H₁' = d → H₁' ≤ H₁ →
          (E₁.baseChange M₁).cyclicQuotientJ H₁' d =
            algebraMap (modularFunctionFieldFullC K N) M₁ ⟨jqNModC K d, jqModCd_mem_full K N hd⟩ := by
  classical

  let M : Type u := AlgebraicClosure (LaurentSeries K)

  have hNF : ((N : ℕ) : modularFunctionFieldFullC K N) ≠ 0 := fun h => hN <|
    (algebraMap K (modularFunctionFieldFullC K N)).injective (by rw [map_natCast, map_zero]; exact h)
  have hNM₁ : (N : M₁) ≠ 0 := fun h => hNF <|
    (algebraMap (modularFunctionFieldFullC K N) M₁).injective (by rw [map_natCast, map_zero]; exact h)
  have hNM : (N : M) ≠ 0 := fun h => hN <|
    (algebraMap K M).injective (by rw [map_natCast, map_zero]; exact h)
  have hdM : ∀ {d : ℕ}, d ∣ N → (d : M) ≠ 0 := by
    rintro d ⟨c, hc⟩ h
    exact hNM (by rw [hc, Nat.cast_mul, h, zero_mul])

  haveI : NeZero (N : K) := ⟨hN⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N

  obtain ⟨P, hP0, hP⟩ : ∃ P : ((tateLaurent K).baseChange M).toAffine.Point,
      (∀ n : ℕ, n • P = 0 ↔ N ∣ n) ∧
      ∀ n : ℕ, ¬ N ∣ n →
        ∃ h : ((tateLaurent K).baseChange M).toAffine.Nonsingular
            (algebraMap (LaurentSeries K) M (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) M (toricPoint K 1 (ζ ^ n)).2),
          n • P = WeierstrassCurve.Affine.Point.some
            (algebraMap (LaurentSeries K) M (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) M (toricPoint K 1 (ζ ^ n)).2) h := by
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · have hN1 : N = 1 := by have := NeZero.ne N; omega
      refine ⟨0, fun n => ?_, fun n hn => (hn (hN1 ▸ one_dvd n)).elim⟩
      rw [hN1, nsmul_zero]
      exact ⟨fun _ => one_dvd n, fun _ => rfl⟩
    · exact ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot K N hge ζ hζ M

  have htate : ∀ (d : ℕ) [NeZero d], d ∣ N →
      ∀ H' : AddSubgroup ((tateLaurent K).baseChange M).toAffine.Point,
        IsAddCyclic H' ∧ Nat.card H' = d → H' ≤ AddSubgroup.zmultiples P →
          ((tateLaurent K).baseChange M).cyclicQuotientJ H' d =
            algebraMap (LaurentSeries K) M (jqNModC K d) :=
    fun d _ hd H' hH' hle =>
      ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples K M N ζ hζ P
        hP0 hP d hd H' hH' hle

  have hordP : addOrderOf P = N := by
    refine Nat.dvd_antisymm ?_ ?_
    · exact addOrderOf_dvd_iff_nsmul_eq_zero.2 ((hP0 N).2 dvd_rfl)
    · exact (hP0 _).1 (addOrderOf_dvd_iff_nsmul_eq_zero.1 dvd_rfl)
  have hμ : IsAddCyclic (AddSubgroup.zmultiples P) ∧ Nat.card (AddSubgroup.zmultiples P) = N :=
    ⟨inferInstance, by rw [Nat.card_zmultiples, hordP]⟩

  haveI instT : ((tateLaurent K).baseChange M).IsElliptic :=
    show ((tateLaurent K).map (algebraMap (LaurentSeries K) M)).IsElliptic from inferInstance
  haveI instE₁M : (E₁.baseChange M).IsElliptic :=
    show (E₁.map (algebraMap (modularFunctionFieldFullC K N) M)).IsElliptic from inferInstance
  have hjT : ((tateLaurent K).baseChange M).j = algebraMap (LaurentSeries K) M (jqModC K) := by
    change ((tateLaurent K).map (algebraMap (LaurentSeries K) M)).j = _
    rw [WeierstrassCurve.map_j, ModularCurve.j_tateLaurent]
  have hjE : (E₁.baseChange M).j = algebraMap (LaurentSeries K) M (jqModC K) := by
    change (E₁.map (algebraMap (modularFunctionFieldFullC K N) M)).j = _
    rw [WeierstrassCurve.map_j, hj, IsScalarTower.algebraMap_apply (modularFunctionFieldFullC K N)
      (LaurentSeries K) M]
    rfl
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (E₁.baseChange M)
    ((tateLaurent K).baseChange M) (hjE.trans hjT.symm)
  obtain ⟨g, hg⟩ := exists_addEquiv_variableChange (E₁.baseChange M) ((tateLaurent K).baseChange M) C hC

  set H₂ : AddSubgroup (E₁.baseChange M).toAffine.Point :=
    (AddSubgroup.zmultiples P).map g.symm.toAddMonoidHom with hH₂def
  have hH₂map : H₂.map g.toAddMonoidHom = AddSubgroup.zmultiples P := by
    ext x
    rw [AddSubgroup.mem_map_equiv, hH₂def, AddSubgroup.mem_map_equiv, AddEquiv.symm_symm,
      AddEquiv.apply_symm_apply]
  have hH₂ : IsAddCyclic H₂ ∧ Nat.card H₂ = N :=
    map_cyclic_card g.symm.toAddMonoidHom g.symm.injective _ hμ

  haveI : Module.IsTorsionFree (modularFunctionFieldFullC K N) M₁ :=
    DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (modularFunctionFieldFullC K N) M :=
    DivisionSemiring.to_moduleIsTorsionFree
  let e₁ : M₁ →ₐ[modularFunctionFieldFullC K N] M := IsAlgClosed.lift
  let f : (E₁.baseChange M₁).toAffine.Point →+ (E₁.baseChange M).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map e₁
  have hf : Function.Injective f := WeierstrassCurve.Affine.Point.map_injective e₁
  have hH₂le : H₂ ≤ f.range := fun Q hQ =>
    torsion_mem_range E₁ e₁ N hNM₁ hNM Q (nsmul_eq_zero_of_mem hH₂.2 hQ)
  obtain ⟨hH₁map, hH₁c, hH₁card⟩ := comap_cyclic_card f hf H₂ hH₂le hH₂
  refine ⟨H₂.comap f, ⟨hH₁c, hH₁card⟩, fun d _ hd H₁' hH₁' hle => ?_⟩

  have hH₂' : IsAddCyclic (H₁'.map f) ∧ Nat.card (H₁'.map f) = d := map_cyclic_card f hf H₁' hH₁'
  have hH₂'le : H₁'.map f ≤ H₂ := (AddSubgroup.map_mono hle).trans hH₁map.le
  have hμ' : IsAddCyclic ((H₁'.map f).map g.toAddMonoidHom) ∧
      Nat.card ((H₁'.map f).map g.toAddMonoidHom) = d :=
    map_cyclic_card g.toAddMonoidHom g.injective _ hH₂'
  have hμ'le : (H₁'.map f).map g.toAddMonoidHom ≤ AddSubgroup.zmultiples P :=
    (AddSubgroup.map_mono hH₂'le).trans hH₂map.le

  have h1 := htate d hd _ hμ' hμ'le
  have h2 := hg (H₁'.map f) d (hdM hd)
  have h3 := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E₁ e₁ H₁' d
  have h4 : algebraMap (LaurentSeries K) M (jqNModC K d) =
      e₁ (algebraMap (modularFunctionFieldFullC K N) M₁ ⟨jqNModC K d, jqModCd_mem_full K N hd⟩) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (modularFunctionFieldFullC K N)
      (LaurentSeries K) M]
    rfl
  apply e₁.toRingHom.injective
  change e₁ _ = e₁ _
  rw [← h4, ← h1, h2]
  exact h3.symm

end P2MKcCH1AllD

open P2MKcCH1AllD AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine in
universe u v w in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Φ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω //
          ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ H).1) ∧
      ∀ (L : Type w) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra k L] [Algebra Ω L]
        [IsScalarTower k Ω L]
        (H : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
        (d : ℕ) [NeZero d] (hd : d ∣ N)
        (H' : {H' : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H' ∧ Nat.card H' = d}),
        H'.1 ≤ H.1 →
          algebraMap Ω L ((Φ H).1 ⟨jqNModC K d, jqModCd_mem_full K N hd⟩) =
            (E.baseChange L).cyclicQuotientJ
              (H'.1.map (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k Ω L))) d := by
  classical
  obtain ⟨Φ, hnat, hval⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ
      K N hN k Ω E hE hfull
  refine ⟨Φ, hnat, ?_⟩
  intro L _ _ _ _ _ _ H d _ hd H' hle
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N

  letI : Algebra K L := ((algebraMap k L).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hNL : (N : L) ≠ 0 := fun h => hN <|
    (algebraMap K L).injective (by rw [map_natCast, map_zero]; exact h)
  have hdL : (d : L) ≠ 0 := by
    obtain ⟨c, hc⟩ := hd
    intro h
    exact hNL (by rw [hc, Nat.cast_mul, h, zero_mul])

  haveI instEL : (E.baseChange L).IsElliptic :=
    show (E.map (algebraMap k L)).IsElliptic from inferInstance
  have hjL : (E.baseChange L).j = algebraMap k L E.j := by
    change (E.map (algebraMap k L)).j = _
    rw [WeierstrassCurve.map_j]
  have hEL : Transcendental K (E.baseChange L).j := by
    rw [hjL]
    exact (transcendental_algebraMap_iff (algebraMap k L).injective).2 hE
  have hinj := (WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
    K N data L hNL (E.baseChange L) hEL).injOn

  let ιL : (E.baseChange Ω).toAffine.Point →+ (E.baseChange L).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k Ω L)
  have hιL : Function.Injective ιL :=
    WeierstrassCurve.Affine.Point.map_injective (IsScalarTower.toAlgHom k Ω L)
  have hHL : IsAddCyclic (H.1.map ιL) ∧ Nat.card (H.1.map ιL) = N := map_cyclic_card ιL hιL _ H.2
  have hH'L : IsAddCyclic (H'.1.map ιL) ∧ Nat.card (H'.1.map ιL) = d := map_cyclic_card ιL hιL _ H'.2
  have hH'Lle : H'.1.map ιL ≤ H.1.map ιL := AddSubgroup.map_mono hle

  set ψ : modularFunctionFieldFullC K N →ₐ[K] Ω := (Φ H).1 with hψdef
  have hψj : ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap k Ω E.j := (Φ H).2
  have hψN : algebraMap Ω L (ψ ⟨jqNModC K N, jqModCd_mem_full K N dvd_rfl⟩) =
      (E.baseChange L).cyclicQuotientJ (H.1.map ιL) N := hval L H
  letI : Algebra (modularFunctionFieldFullC K N) L := ((algebraMap Ω L).comp ψ.toRingHom).toAlgebra
  have halgFL : ∀ x : modularFunctionFieldFullC K N,
      algebraMap (modularFunctionFieldFullC K N) L x = algebraMap Ω L (ψ x) := fun _ => rfl

  set jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩ with hjFdef
  let E_F : WeierstrassCurve (modularFunctionFieldFullC K N) := WeierstrassCurve.ofJ jF
  have hjEF : E_F.j = jF := WeierstrassCurve.ofJ_j jF
  haveI instEFL : (E_F.baseChange L).IsElliptic :=
    show (E_F.map (algebraMap (modularFunctionFieldFullC K N) L)).IsElliptic from inferInstance
  have hj2 : (E_F.baseChange L).j = (E.baseChange L).j := by
    change (E_F.map (algebraMap (modularFunctionFieldFullC K N) L)).j = _
    rw [WeierstrassCurve.map_j, hjEF, hjL, halgFL, hjFdef, hψj, ← IsScalarTower.algebraMap_apply]
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (E_F.baseChange L)
    (E.baseChange L) hj2
  obtain ⟨g, hg⟩ := exists_addEquiv_variableChange (E_F.baseChange L) (E.baseChange L) C hC

  let M₁ : Type u := AlgebraicClosure (modularFunctionFieldFullC K N)
  obtain ⟨H₁, hH₁, hT⟩ := tate_witness K N hN M₁ E_F hjEF
  haveI : Module.IsTorsionFree (modularFunctionFieldFullC K N) M₁ :=
    DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (modularFunctionFieldFullC K N) L :=
    DivisionSemiring.to_moduleIsTorsionFree
  let τ : M₁ →ₐ[modularFunctionFieldFullC K N] L := IsAlgClosed.lift
  let fτ : (E_F.baseChange M₁).toAffine.Point →+ (E_F.baseChange L).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map τ
  have hfτ : Function.Injective fτ := WeierstrassCurve.Affine.Point.map_injective τ
  have hbc : ∀ (H₀ : AddSubgroup (E_F.baseChange M₁).toAffine.Point) (n : ℕ),
      (E_F.baseChange L).cyclicQuotientJ (H₀.map fτ) n = τ ((E_F.baseChange M₁).cyclicQuotientJ H₀ n) :=
    fun H₀ n => WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E_F τ H₀ n
  have hτalg : ∀ x : modularFunctionFieldFullC K N,
      τ (algebraMap (modularFunctionFieldFullC K N) M₁ x) = algebraMap Ω L (ψ x) := fun x => by
    rw [AlgHom.commutes, halgFL]

  let G : (E_F.baseChange M₁).toAffine.Point →+ (E.baseChange L).toAffine.Point :=
    g.toAddMonoidHom.comp fτ
  have hG : Function.Injective G := g.injective.comp hfτ
  have hGmap : ∀ H₀ : AddSubgroup (E_F.baseChange M₁).toAffine.Point,
      H₀.map G = (H₀.map fτ).map g.toAddMonoidHom := fun H₀ => (AddSubgroup.map_map _ _ _).symm
  have hGval : ∀ (H₀ : AddSubgroup (E_F.baseChange M₁).toAffine.Point) (n : ℕ), (n : L) ≠ 0 →
      (E.baseChange L).cyclicQuotientJ (H₀.map G) n = τ ((E_F.baseChange M₁).cyclicQuotientJ H₀ n) := by
    intro H₀ n hn
    rw [hGmap, hg _ n hn, hbc]
  have hH₃ : IsAddCyclic (H₁.map G) ∧ Nat.card (H₁.map G) = N := map_cyclic_card G hG _ hH₁

  have hval₃ : (E.baseChange L).cyclicQuotientJ (H₁.map G) N =
      (E.baseChange L).cyclicQuotientJ (H.1.map ιL) N := by
    rw [hGval H₁ N hNL, hT N dvd_rfl H₁ hH₁ le_rfl, hτalg, hψN]
  have hEq : H₁.map G = H.1.map ιL := hinj hH₃ hHL hval₃

  have hH'range : H'.1.map ιL ≤ G.range :=
    hH'Lle.trans (hEq.symm.le.trans (AddSubgroup.map_le_range _ _))
  obtain ⟨hH₁'map, hH₁'c, hH₁'card⟩ := comap_cyclic_card G hG (H'.1.map ιL) hH'range hH'L
  have hH₁'le : (H'.1.map ιL).comap G ≤ H₁ := by
    have := AddSubgroup.comap_mono (f := G) (hH'Lle.trans hEq.symm.le)
    rwa [AddSubgroup.comap_map_eq_self_of_injective hG] at this

  rw [← hH₁'map, hGval _ d hdL, hT d hd _ ⟨hH₁'c, hH₁'card⟩ hH₁'le, hτalg]

end S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
end P2MW
export P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ (solution)
