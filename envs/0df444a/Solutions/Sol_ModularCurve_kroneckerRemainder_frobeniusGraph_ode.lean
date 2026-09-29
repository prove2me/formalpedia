-- Prove2me | solution 1 for ModularCurve.kroneckerRemainder_frobeniusGraph_ode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e2ef4edc-7948-5015-8585-18e0fa251106

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul
import Theorems.Thm_ModularCurve_laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow
import Theorems.Thm_ModularCurve_thetaL_laurentMap_dworkQuotient
import Theorems.Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerRemainder_frobeniusGraph_ode
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "HahnSeries Polynomial ModularCurve P2MW.S_ModularCurve_kroneckerRemainder_frobeniusGraph_ode.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData laurentMap laurentMap_coeff laurentMap_single laurentMap_ofPowerSeries jqInt coeff_jqInt_neg_one evalAtJInt jqModC thetaL thetaL_apply existsUnique_qExpand_sub_pow_eq_natCast_mul laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow thetaL_laurentMap_dworkQuotient thetaL_jqModC_pow_mul_prod_sq_eq transcendental_jqModC"
namespace K2ODE
p2m_open "ModularCurve"

section ThetaR

variable {R : Type*} [CommRing R]

noncomputable def thetaR (f : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f

theorem coeff_single_one_mul_derivative_add_one (f : LaurentSeries R) (m : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff (m + 1) =
      ((m + 1 : ℤ) : R) * f.coeff (m + 1) := by
  rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  simp only [Nat.cast_one]

theorem coeff_single_one_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  have h := coeff_single_one_mul_derivative_add_one f (n - 1)
  simp only [sub_add_cancel] at h
  exact h

theorem coeff_thetaR (f : LaurentSeries R) (n : ℤ) : (thetaR f).coeff n = (n : R) * f.coeff n :=
  coeff_single_one_mul_derivative f n

theorem thetaR_add (f g : LaurentSeries R) : thetaR (f + g) = thetaR f + thetaR g := by
  ext n; simp [coeff_thetaR, mul_add]

theorem thetaR_sub (f g : LaurentSeries R) : thetaR (f - g) = thetaR f - thetaR g := by
  ext n; simp [coeff_thetaR, mul_sub]

theorem thetaR_natCast_mul (m : ℕ) (f : LaurentSeries R) :
    thetaR ((m : LaurentSeries R) * f) = (m : LaurentSeries R) * thetaR f := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) m, HahnSeries.C_mul_eq_smul,
    HahnSeries.C_mul_eq_smul, coeff_thetaR, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    coeff_thetaR, smul_eq_mul, smul_eq_mul]
  ring

theorem support_thetaR_subset (f : LaurentSeries R) : (thetaR f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, coeff_thetaR] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

theorem thetaR_mul (f g : LaurentSeries R) : thetaR (f * g) = thetaR f * g + f * thetaR g := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaR, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (support_thetaR_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_thetaR_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  rw [coeff_thetaR, coeff_thetaR, ← hsum, Int.cast_add]
  ring

theorem thetaR_pow (f : LaurentSeries R) (m : ℕ) :
    thetaR (f ^ (m + 1)) = ((m + 1 : ℕ) : LaurentSeries R) * (f ^ m * thetaR f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, thetaR_mul, ih]
    push_cast
    ring

theorem thetaR_qExpand (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    thetaR (qExpand R N f) = (N : LaurentSeries R) * qExpand R N (thetaR f) := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) N, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul, coeff_thetaR]
  by_cases hn : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeff_thetaR, Int.cast_mul, Int.cast_natCast]
    ring
  · rw [qExpand_coeff_of_not_dvd N _ hn, qExpand_coeff_of_not_dvd N _ hn, mul_zero, mul_zero]

theorem laurentMap_thetaR {k : Type*} [Field k] (φ : R →+* k) (f : LaurentSeries R) :
    laurentMap φ (thetaR f) = thetaL k (laurentMap φ f) := by
  ext n
  rw [thetaL_apply, coeff_single_one_mul_derivative, laurentMap_coeff, coeff_thetaR, map_mul,
    map_intCast, laurentMap_coeff]

end ThetaR

section OverField

variable {k : Type*} [Field k]

theorem thetaL_eq_thetaR (f : LaurentSeries k) : thetaL k f = thetaR f := rfl

theorem thetaR_C' (a : k) : thetaR (HahnSeries.C a : LaurentSeries k) = 0 := by
  ext n
  rw [coeff_thetaR, HahnSeries.coeff_zero]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn, mul_zero]

theorem thetaR_pow' (f : LaurentSeries k) (n : ℕ) :
    thetaR (f ^ n) = (n : LaurentSeries k) * (f ^ (n - 1) * thetaR f) := by
  cases n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← HahnSeries.C_one]
    exact thetaR_C' 1
  | succ m => rw [thetaR_pow, Nat.add_sub_cancel]

theorem thetaL_aeval (J : LaurentSeries k) (P : Polynomial k) :
    thetaL k (aeval J P) = aeval J (derivative P) * thetaL k J := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq]
  | monomial n a =>
    rw [derivative_monomial, aeval_monomial, aeval_monomial, LaurentSeries.algebraMap_apply,
      LaurentSeries.algebraMap_apply, thetaL_eq_thetaR, thetaL_eq_thetaR, thetaR_mul, thetaR_C', zero_mul,
      zero_add, thetaR_pow', map_mul, map_natCast]
    ring

end OverField

theorem laurentMap_jqInt_eq_jqModC (k : Type*) [CommRing k] :
    laurentMap (Int.castRingHom k) jqInt = jqModC k := by
  rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
  rfl

theorem laurentMap_evalAtJInt (k : Type*) [Field k] (P : Polynomial ℤ) :
    laurentMap (Int.castRingHom k) (evalAtJInt P) =
      aeval (laurentMap (Int.castRingHom k) jqInt) (P.map (Int.castRingHom k)) := by
  have h : (laurentMap (Int.castRingHom k)).comp evalAtJInt =
      (aeval (laurentMap (Int.castRingHom k) jqInt)).toRingHom.comp (mapRingHom (Int.castRingHom k)) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp [evalAtJInt]
    · simp [evalAtJInt]
  exact RingHom.congr_fun h P

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    let G : Polynomial k := (R.eval (Polynomial.X ^ q)).map (Int.castRingHom k)
    let F : Polynomial k := Polynomial.X ^ (q ^ 2) - Polynomial.X
    let s : Polynomial k := ∏ a ∈ S₀ \ {0, 1728}, (Polynomial.X - Polynomial.C a)
    (Polynomial.derivative G * F - G * Polynomial.derivative F) * s ^ 2 =
      (Polynomial.X ^ (q - 1) * s ^ 2
        - Polynomial.X ^ (8 * m + 2 * e₄ + 4 * e₆) * (Polynomial.X - Polynomial.C 1728) ^ (6 * m + 2 * e₄ + 2 * e₆)) * F ^ 2 := by
  intro G F s
  have hp : q.Prime := Fact.out
  set ι := Int.castRingHom k with hι
  set J : LaurentSeries k := laurentMap ι jqInt with hJ
  have hJC : jqModC k = J := (laurentMap_jqInt_eq_jqModC k).symm
  set θ := thetaL k with hθ

  have hinj : Function.Injective (aeval J : Polynomial k →ₐ[k] LaurentSeries k) := by
    rw [← hJC]; exact transcendental_iff_injective.mp (transcendental_jqModC k)

  obtain ⟨S, hS, -⟩ := existsUnique_qExpand_sub_pow_eq_natCast_mul q jqInt
  have hA : aeval J G = - laurentMap ι S * aeval J F := by
    have h := laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow q data R hR S hS k
    rw [laurentMap_evalAtJInt] at h
    rw [h]
    simp [F, hJ, hι]
  have hB : θ (laurentMap ι S) = θ J ^ q - J ^ (q - 1) * θ J :=
    thetaL_laurentMap_dworkQuotient q S hS k
  have hC : θ J ^ (q - 1) * aeval J s ^ 2 =
      J ^ (8 * m + 2 * e₄ + 4 * e₆) * (J - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by
    have h := thetaL_jqModC_pow_mul_prod_sq_eq q hq m e₄ e₆ hm he₄ he₆ k S₀ hS₀
    rw [hJC] at h
    have hs : aeval J s = ∏ a ∈ S₀ \ {0, 1728}, (J - HahnSeries.C a) := by
      simp only [s, map_prod, map_sub, aeval_X, aeval_C, LaurentSeries.algebraMap_apply]
    rw [hs]
    exact h

  have hF' : derivative F = -1 := by
    simp only [F, derivative_sub, derivative_X_pow, derivative_X, Nat.cast_pow]
    rw [CharP.cast_eq_zero k q] ; simp

  have hθJ : θ J ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : LaurentSeries k => x.coeff (-1)) h0
    simp only [hθ, thetaL_eq_thetaR, coeff_thetaR, HahnSeries.coeff_zero, hJ, laurentMap_coeff,
      coeff_jqInt_neg_one, map_one, Int.cast_neg, Int.cast_one, mul_one, neg_eq_zero] at h1
    exact one_ne_zero h1

  have hq1 : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hp.pos).symm
  have hstar : aeval J (derivative G) * aeval J F + aeval J G =
      (J ^ (q - 1) - θ J ^ (q - 1)) * aeval J F ^ 2 := by
    have h1 := congrArg θ hA
    rw [hθ, thetaL_aeval, neg_mul, map_neg, thetaL_eq_thetaR (laurentMap ι S * aeval J F), thetaR_mul,
      ← thetaL_eq_thetaR, ← thetaL_eq_thetaR, thetaL_aeval, hF', ← hθ, hB] at h1
    simp only [map_neg, map_one] at h1

    have h2 : θ J * (aeval J (derivative G) * aeval J F + aeval J G
        - (J ^ (q - 1) - θ J ^ (q - 1)) * aeval J F ^ 2) = 0 := by
      have e : θ J ^ q = θ J ^ (q - 1) * θ J := by
        conv_lhs => rw [hq1]
        rw [pow_succ]
      rw [e] at h1
      linear_combination (aeval J F) * h1 + (θ J) * hA
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hθJ
    · exact sub_eq_zero.mp h

  apply hinj
  simp only [map_mul, map_sub, map_pow, hF', map_neg, map_one, aeval_X, map_ofNat]
  rw [← hC]
  linear_combination (aeval J s ^ 2) * hstar

end ModularCurve.K2ODE

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    let G : Polynomial k := (R.eval (Polynomial.X ^ q)).map (Int.castRingHom k)
    let F : Polynomial k := Polynomial.X ^ (q ^ 2) - Polynomial.X
    let s : Polynomial k := ∏ a ∈ S₀ \ {0, 1728}, (Polynomial.X - Polynomial.C a)
    (Polynomial.derivative G * F - G * Polynomial.derivative F) * s ^ 2 =
      (Polynomial.X ^ (q - 1) * s ^ 2
        - Polynomial.X ^ (8 * m + 2 * e₄ + 4 * e₆) * (Polynomial.X - Polynomial.C 1728) ^ (6 * m + 2 * e₄ + 2 * e₆)) * F ^ 2 :=
  ModularCurve.K2ODE.main q hq data R hR m e₄ e₆ hm he₄ he₆ k S₀ hS₀

end S_ModularCurve_kroneckerRemainder_frobeniusGraph_ode
end P2MW
export P2MW.S_ModularCurve_kroneckerRemainder_frobeniusGraph_ode (solution)
