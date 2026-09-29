-- Prove2me | solution 1 for ModularCurve.cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/47f767cc-8eae-520b-bac7-1db1d7107d62

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Theorems.Thm_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

set_option maxHeartbeats 3200000 in

theorem solution
    (F : Type) [Field F] [DecidableEq F] (Λ : Type) [Field Λ] [DecidableEq Λ] [Algebra (LaurentSeries F) Λ]
    (w M' : ℕ) [NeZero w] [NeZero M'] (hM'F : ((M' : ℕ) : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ M')
    (C : WeierstrassCurve.VariableChange Λ)
    (g : (C • (ModularCurve.tateBase F w).baseChange Λ).toAffine.Point)
    (hg0 : ∀ n : ℕ, n • g = 0 ↔ M' ∣ n)
    (hg : ∀ n : ℕ, ¬ M' ∣ n →
        ∃ h₁ : ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).1)
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F w (ζ ^ n)).2),
          WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) (n • g) =
            WeierstrassCurve.Affine.Point.some _ _ h₁)
    (d : ℕ) [NeZero d] (hd : d ∣ M') :
    (C • (ModularCurve.tateBase F w).baseChange Λ).cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g)) d =
      algebraMap (LaurentSeries F) Λ (ModularCurve.jqNModC F (w * d)) := by
  classical

  set a : LaurentSeries F →+* Λ := algebraMap (LaurentSeries F) Λ with ha

  have hvc_add : ∀ P Q : (C • ((ModularCurve.tateBase F w).baseChange Λ)).toAffine.Point,
      WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) (P + Q) =
        WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) P + WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) Q := by
    intro P Q
    have hinj : Function.Injective (WeierstrassCurve.Affine.Point.vcInvFun C ((ModularCurve.tateBase F w).baseChange Λ).toAffine) :=
      (WeierstrassCurve.Affine.Point.vcFun_rightInverse (C := C) (W := ((ModularCurve.tateBase F w).baseChange Λ).toAffine)).injective
    apply hinj
    rw [WeierstrassCurve.Affine.Point.vcInvFun_add, WeierstrassCurve.Affine.Point.vcFun_leftInverse,
      WeierstrassCurve.Affine.Point.vcFun_leftInverse, WeierstrassCurve.Affine.Point.vcFun_leftInverse]
  let φ : (C • ((ModularCurve.tateBase F w).baseChange Λ)).toAffine.Point →+ ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Point :=
    { toFun := WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ)
      map_zero' := WeierstrassCurve.Affine.Point.vcFun_zero
      map_add' := hvc_add }
  have hφ : ∀ P, φ P = WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F w).baseChange Λ) P := fun _ => rfl
  have hφinj : Function.Injective φ :=
    (WeierstrassCurve.Affine.Point.vcFun_leftInverse (C := C) (W := ((ModularCurve.tateBase F w).baseChange Λ).toAffine)).injective
  set P₀ : ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Point := φ g with hP₀

  have hd0 : ((d : ℕ) : Λ) ≠ 0 := by
    intro h0
    apply hM'F
    obtain ⟨c, rfl⟩ := hd
    have hdF : ((d : ℕ) : F) = 0 :=
      ((algebraMap (LaurentSeries F) Λ).comp (algebraMap F (LaurentSeries F))).injective
        (by rw [map_natCast, map_zero]; exact h0)
    rw [Nat.cast_mul, hdF, zero_mul]
  have step1 : (C • ((ModularCurve.tateBase F w).baseChange Λ)).cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g)) d =
      ((ModularCurve.tateBase F w).baseChange Λ).cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • P₀)) d := by
    refine WeierstrassCurve.cyclicQuotientJ_variableChange_eq C ((ModularCurve.tateBase F w).baseChange Λ) _ _ (fun P => ?_) d hd0
    rw [← hφ, AddSubgroup.mem_zmultiples_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [hP₀, ← map_nsmul φ, ← map_zsmul φ]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, hφinj ?_⟩
      rw [map_zsmul φ, map_nsmul φ, ← hP₀, hk]
  rw [step1]
  have hP0' : ∀ n : ℕ, n • P₀ = 0 ↔ M' ∣ n := by
    intro n
    rw [hP₀, ← map_nsmul φ, ← hg0 n]
    constructor
    · intro h; exact hφinj (by rw [h, φ.map_zero])
    · intro h; rw [h, φ.map_zero]
  have hordP : addOrderOf P₀ = M' := by
    apply Nat.dvd_antisymm
    · exact addOrderOf_dvd_of_nsmul_eq_zero ((hP0' M').mpr dvd_rfl)
    · exact (hP0' _).mp (addOrderOf_nsmul_eq_zero P₀)
  have hM0 : M' ≠ 0 := NeZero.ne M'
  have hdvd : M' / d ∣ M' := Nat.div_dvd_of_dvd hd
  have hordQ : addOrderOf ((M' / d) • P₀) = d := by
    have hn0 : M' / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd) (Nat.pos_of_ne_zero (NeZero.ne d))).ne'
    rw [addOrderOf_nsmul_of_dvd hn0 (by rw [hordP]; exact hdvd), hordP, Nat.div_div_self hd hM0]
  have hH' : IsAddCyclic (AddSubgroup.zmultiples ((M' / d) • P₀)) ∧
      Nat.card (AddSubgroup.zmultiples ((M' / d) • P₀)) = d :=
    ⟨inferInstance, by rw [Nat.card_zmultiples, hordQ]⟩
  have hle : AddSubgroup.zmultiples ((M' / d) • P₀) ≤ AddSubgroup.zmultiples P₀ :=
    AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _)
  have hPtoric' : ∀ n : ℕ, ¬ M' ∣ n →
      ∃ h : ((ModularCurve.tateBase F w).baseChange Λ).toAffine.Nonsingular (a (ModularCurve.toricPoint F w (ζ ^ n)).1)
          (a (ModularCurve.toricPoint F w (ζ ^ n)).2),
        n • P₀ = WeierstrassCurve.Affine.Point.some _ _ h := by
    intro n hn
    obtain ⟨h₁, hsome⟩ := hg n hn
    exact ⟨h₁, by rw [hP₀, ← map_nsmul φ, hφ, hsome]⟩

  let alg' : Algebra (LaurentSeries F) Λ := (a.comp (ModularCurve.qExpand F w)).toAlgebra
  have h1 : ∀ c : F, @algebraMap (LaurentSeries F) Λ _ _ alg' (ModularCurve.toricPoint F 1 c).1 =
      a (ModularCurve.toricPoint F w c).1 := by
    intro c
    have hlev := ModularCurve.toricPoint_level_mul F 1 w c
    rw [mul_one] at hlev
    rw [hlev]; rfl
  have h2 : ∀ c : F, @algebraMap (LaurentSeries F) Λ _ _ alg' (ModularCurve.toricPoint F 1 c).2 =
      a (ModularCurve.toricPoint F w c).2 := by
    intro c
    have hlev := ModularCurve.toricPoint_level_mul F 1 w c
    rw [mul_one] at hlev
    rw [hlev]; rfl
  have step2 := @ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples F _ Λ _ _ alg'
    M' _ ζ hζ P₀ hP0' (fun n hn => by rw [h1, h2]; exact hPtoric' n hn) d _ hd
    (AddSubgroup.zmultiples ((M' / d) • P₀)) hH' hle
  refine step2.trans ?_
  show a (ModularCurve.qExpand F w (ModularCurve.jqNModC F d)) = a (ModularCurve.jqNModC F (w * d))
  rw [ModularCurve.jqNModC, ModularCurve.jqNModC, ModularCurve.qExpand_qExpand]

end S_ModularCurve_cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width
end P2MW
export P2MW.S_ModularCurve_cyclicQuotientJ_smul_tateBase_baseChange_zmultiples_eq_algebraMap_jqNModC_width (solution)
