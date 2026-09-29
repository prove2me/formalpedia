-- Prove2me | solution 1 for ModularCurve.le_span_setOf_logarithmic_of_frobPushDiffModL_surjOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/65e41745-a2f6-5e39-b49b-b9cc60ff03d7

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Theorems.Thm_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed
import Theorems.Thm_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Theorems.Thm_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_le_span_setOf_logarithmic_of_frobPushDiffModL_surjOn
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.cechH1.traceAlong_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace LogSpan

open ModularCurve HahnSeries IntermediateField AlgebraicCurve AlgebraicCurve.KwPke AlgebraicCurve.KwCart

section Laurent

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

theorem coeff_pow_char_mul (s : LaurentSeries k) (m : ℤ) :
    (s ^ p).coeff (m * p) = (s.coeff m) ^ p := by
  rw [pow_char_eq_map_frobenius_qExpand p s, HahnSeries.map_coeff, mul_comm,
    qExpand_coeff_mul, frobenius_def]

theorem coeff_pow_char_of_not_dvd (s : LaurentSeries k) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    (s ^ p).coeff n = 0 := by
  rw [pow_char_eq_map_frobenius_qExpand p s, HahnSeries.map_coeff,
    qExpand_coeff_of_not_dvd p s hn, map_zero]

theorem coeff_mul_eq_zero_of_support (x z : LaurentSeries k)
    (hx : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → x.coeff n = 0) (hz : ∀ m : ℤ, z.coeff (m * p) = 0) (n : ℤ) :
    (x * z).coeff (n * p) = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  by_cases hi : (p : ℤ) ∣ ij.1
  · obtain ⟨c, hc⟩ := hi
    have hj : ij.2 = (n - c) * p := by
      have : ij.2 = n * p - ij.1 := by rw [← hsum]; ring
      rw [this, hc]; ring
    rw [hj, hz, mul_zero]
  · rw [hx _ hi, zero_mul]

theorem coeff_pow_mul_eq_pow (h z w : LaurentSeries k)
    (hzw : ∀ m : ℤ, z.coeff (m * p) = (w.coeff m) ^ p) (n : ℤ) :
    (h ^ p * z).coeff (n * p) = ((h * w).coeff n) ^ p := by
  have hsplit : h ^ p * z = (h * w) ^ p + h ^ p * (z - w ^ p) := by ring
  rw [hsplit, HahnSeries.coeff_add, coeff_pow_char_mul p (h * w) n,
    coeff_mul_eq_zero_of_support p (h ^ p) (z - w ^ p) (fun m hm => coeff_pow_char_of_not_dvd p h hm)
      (fun m => by rw [HahnSeries.coeff_sub, hzw, coeff_pow_char_mul p w m, sub_self]) n,
    add_zero]

theorem coeff_thetaL_mul_char (y : LaurentSeries k) (m : ℤ) :
    (thetaL k y).coeff (m * p) = 0 := by
  rw [thetaL_apply, theta_coeff, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
    CharP.cast_eq_zero k p, mul_zero, zero_mul]

theorem thetaL_pow_succ (T : LaurentSeries k) (i : ℕ) :
    thetaL k (T ^ (i + 1)) = (i + 1) • (T ^ i * thetaL k T) := by
  induction i with
  | zero => rw [zero_add, pow_one, pow_zero, one_mul, one_smul]
  | succ i ih =>
    rw [pow_succ, thetaL_apply, theta_mul, ← thetaL_apply, ← thetaL_apply, ih, mul_smul_comm,
      ← mul_assoc, ← pow_succ', add_comm, ← succ_nsmul]

theorem coeff_pow_mul_thetaL_eq_zero (T : LaurentSeries k) {i : ℕ} (hi : ((i + 1 : ℕ) : k) ≠ 0)
    (m : ℤ) : (T ^ i * thetaL k T).coeff (m * p) = 0 := by
  have h := congrArg (fun y : LaurentSeries k => y.coeff (m * p)) (thetaL_pow_succ (k := k) T i)
  beta_reduce at h
  rw [coeff_thetaL_mul_char p, HahnSeries.coeff_nsmul, Pi.smul_apply, nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h.symm with h0 | h0
  · exact absurd h0 hi
  · exact h0

theorem coeff_pow_pred_mul_thetaL (T : LaurentSeries k) (m : ℤ) :
    (T ^ (p - 1) * thetaL k T).coeff (m * p) = ((thetaL k T).coeff m) ^ p := by
  by_cases hT : T = 0
  · subst hT
    rw [map_zero, mul_zero, HahnSeries.coeff_zero, HahnSeries.coeff_zero,
      zero_pow hp.out.ne_zero]
  · have hrw : T ^ (p - 1) * thetaL k T = T ^ p * (T⁻¹ * thetaL k T) := by
      rw [← mul_assoc, ← pow_sub_one_mul hp.out.ne_zero, mul_assoc (T ^ (p - 1)),
        mul_inv_cancel₀ hT, mul_one]
    rw [hrw, coeff_pow_mul_eq_pow p T _ (T⁻¹ * thetaL k T)
      (fun m' => coeff_inv_mul_thetaL_mul_char_eq_pow k p T hT m') m, ← mul_assoc,
      mul_inv_cancel₀ hT, one_mul]

omit hp [CharP k p] in

theorem thetaL_coeffMap (τ : k →+* k) (s : LaurentSeries k) :
    thetaL k (coeffMap τ s) = coeffMap τ (thetaL k s) := by
  ext n
  simp only [thetaL_apply, theta_coeff, coeffMap_coeff, map_zsmul]

theorem qDecimate_eq_coeffMap_frobenius {z w : LaurentSeries k}
    (h : ∀ m : ℤ, z.coeff (m * p) = (w.coeff m) ^ p) :
    qDecimate k p z = coeffMap (frobenius k p) w := by
  ext m
  rw [coeff_qDecimate, coeffMap_coeff, frobenius_def, mul_comm, h]

theorem coeffMap_frobenius_injective :
    Function.Injective (coeffMap (frobenius k p) : LaurentSeries k → LaurentSeries k) := by
  intro x y h
  ext n
  have := congrArg (fun s : LaurentSeries k => s.coeff n) h
  simp only [coeffMap_coeff] at this
  exact frobenius_inj k p this

end Laurent

section Sep

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehler_adjoin_eq_zero {t : F}
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (ω : Ω[F⁄K⟮t⟯]) : ω = 0 := by
  have hsurj : Function.Surjective (KaehlerDifferential.map K K⟮t⟯ F F) :=
    KaehlerDifferential.map_surjective_of_surjective K K⟮t⟯ F F Function.surjective_id
  have hzero : KaehlerDifferential.map K K⟮t⟯ F F = 0 := by
    have hle : (⊤ : Submodule F Ω[F⁄K]) ≤ LinearMap.ker (KaehlerDifferential.map K K⟮t⟯ F F) := by
      rw [← hspan, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        LinearMap.mem_ker, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
      exact (KaehlerDifferential.D K⟮t⟯ F).map_algebraMap (AdjoinSimple.gen K t)
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp hle)
  obtain ⟨η, rfl⟩ := hsurj ω
  rw [hzero, LinearMap.zero_apply]

theorem isSeparable_adjoin_of_span_D_eq_top [Algebra.EssFiniteType K F] {t : F}
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) :
    Algebra.IsSeparable K⟮t⟯ F := by
  haveI : Subsingleton Ω[F⁄K⟮t⟯] := ⟨fun a b => by
    rw [kaehler_adjoin_eq_zero hspan a, kaehler_adjoin_eq_zero hspan b]⟩
  haveI : Algebra.FormallyUnramified K⟮t⟯ F := ⟨inferInstance⟩
  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact Algebra.FormallyUnramified.isSeparable K⟮t⟯ F

theorem isSeparable_of_subfield_le {A B : Subfield F} (hAB : A ≤ B) {x : F}
    (hx : IsSeparable A x) : IsSeparable B x := by
  letI : Algebra A B := (Subfield.inclusion hAB).toAlgebra
  haveI : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsSeparable.tower_top B hx

variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem algebraMap_mem_pthPowers [CharP K p] [PerfectField K] (c : K) :
    algebraMap K F c ∈ kw_pke_pthPowers F p := by
  haveI := PerfectField.toPerfectRing (K := K) p
  obtain ⟨c', hc'⟩ := surjective_frobenius K p c
  rw [kw_pke_mem_pthPowers_iff]
  exact ⟨algebraMap K F c', by rw [← map_pow, ← frobenius_def, hc']⟩

theorem hsep_of_span_D_eq_top [CharP K p] [PerfectField K] [Algebra.EssFiniteType K F] {t : F}
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) (x : F) :
    IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x := by
  haveI := isSeparable_adjoin_of_span_D_eq_top hspan
  have hx : IsSeparable K⟮t⟯ x := Algebra.IsSeparable.isSeparable K⟮t⟯ x
  have hle : K⟮t⟯.toSubfield ≤ (kw_pke_expansionField (ℓ := p) t).toSubfield := by
    change Subfield.closure (Set.range (algebraMap K F) ∪ {t}) ≤ _
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · exact ((kw_pke_expansionField (ℓ := p) t).algebraMap_mem
        ⟨algebraMap K F c, algebraMap_mem_pthPowers c⟩ :)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self _ y
  exact isSeparable_of_subfield_le hle hx

end Sep

section CartierCoord

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]
variable (C : Ω[F⁄K] →+ Ω[F⁄K])
  (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
  (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)

include hsemi hker in

theorem apply_pow_smul_D_eq_zero (t : F) {i : ℕ} (hi : ((i + 1 : ℕ) : F) ≠ 0) :
    C (t ^ i • KaehlerDifferential.D K F t) = 0 := by
  set a : F := ((i + 1 : ℕ) : F)⁻¹ with ha
  have hn : ((i + 1 : ℕ) : F) ^ p = ((i + 1 : ℕ) : F) := by
    rw [← frobenius_def, map_natCast]
  have hap : a ^ p = a := by
    rw [ha, inv_pow, hn]
  have hD : KaehlerDifferential.D K F (t ^ (i + 1)) =
      ((i + 1 : ℕ) : F) • (t ^ i • KaehlerDifferential.D K F t) := by
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_smul, ← Nat.cast_smul_eq_nsmul F,
      smul_smul, mul_comm]
  have hrw : t ^ i • KaehlerDifferential.D K F t =
      a ^ p • KaehlerDifferential.D K F (t ^ (i + 1)) := by
    rw [hap, hD, smul_smul, ha, inv_mul_cancel₀ hi, one_smul]
  rw [hrw, hsemi, hker, smul_zero]

variable (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)

def lastIdx : Fin p := ⟨p - 1, Nat.sub_lt hp.out.pos Nat.one_pos⟩

omit [CharP F p] in
theorem val_lastIdx : ((lastIdx : Fin p) : ℕ) = p - 1 := rfl

theorem natCast_succ_ne_zero {i : Fin p} (hi : i ≠ lastIdx) : ((i + 1 : ℕ) : F) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff F p] at h
  have hlt : (i : ℕ) + 1 < p := by
    have h1 : (i : ℕ) < p := i.2
    have h2 : (i : ℕ) ≠ p - 1 := fun h' => hi (Fin.ext (by rw [h', val_lastIdx]))
    omega
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) h) (not_le.mpr hlt)

include hsemi hker hlog in

theorem apply_sum_pow_smul (s : F) (g : Fin p → F) :
    C (∑ i : Fin p, g i ^ p • (s ^ (i : ℕ) • KaehlerDifferential.D K F s)) =
      g lastIdx • KaehlerDifferential.D K F s := by
  rw [map_sum, Finset.sum_eq_single (lastIdx : Fin p)]
  · rw [hsemi, val_lastIdx, hlog]
  · intro i _ hi
    rw [hsemi, apply_pow_smul_D_eq_zero C hsemi hker s (natCast_succ_ne_zero hi), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
  (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
  (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x)
  (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)

def coordRoot (ω : Ω[F⁄K]) (i : Fin p) : F :=
  kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω) i)

theorem eq_sum_coordRoot_pow_smul (ω : Ω[F⁄K]) :
    ω = ∑ i : Fin p, coordRoot t hdt hspan hsep hdeg ω i ^ p •
      (t ^ (i : ℕ) • KaehlerDifferential.D K F t) := by
  conv_lhs => rw [kw_cart_dtCoord_spec t hdt hspan ω,
    kw_cart_repr_spec t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, coordRoot, kw_cart_root_pow]

include hsemi hker hlog in

theorem apply_eq_coordRoot_last_smul (ω : Ω[F⁄K]) :
    C ω = coordRoot t hdt hspan hsep hdeg ω lastIdx • KaehlerDifferential.D K F t := by
  conv_lhs => rw [eq_sum_coordRoot_pow_smul t hdt hspan hsep hdeg ω]
  exact apply_sum_pow_smul C hsemi hker hlog t _

end CartierCoord

section CartierQExp

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p] [CharP F p] [PerfectField K]
  [AlgebraicCurve.IsCurveOver K F]

theorem coeff_qexp_cartier_pow
    (hft : Algebra.EssFiniteType K F) (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (σ : F →ₐ[K] LaurentSeries K) (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (ω : Ω[F⁄K]) (n : ℤ) :
    (qExpansionDiffAlong σ (C ω)).coeff n ^ p = (qExpansionDiffAlong σ ω).coeff (n * p) := by
  haveI := hft
  have hspan := kw_cart_hspan_of_isCurveOver hdt
  have hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x :=
    hsep_of_span_D_eq_top (K := K) (p := p) hspan
  have hdeg := kw_cart_minpoly_natDegree_eq (ℓ := p) hdt
  have hω := eq_sum_coordRoot_pow_smul t hdt hspan hsep hdeg ω
  have hC := apply_eq_coordRoot_last_smul C hsemi hker hlog t hdt hspan hsep hdeg ω
  set g := coordRoot t hdt hspan hsep hdeg ω with hg
  set T : LaurentSeries K := σ t with hT
  have hqC : qExpansionDiffAlong σ (C ω) = σ (g lastIdx) * thetaL K T := by
    rw [hC, qExpansionDiffAlong_smul, qExpansionDiffAlong_D]
  have hqω : qExpansionDiffAlong σ ω =
      ∑ i : Fin p, σ (g i) ^ p * (T ^ (i : ℕ) * thetaL K T) := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_smul, qExpansionDiffAlong_D, map_pow,
      map_pow]
  rw [hqC, hqω, HahnSeries.coeff_sum, Finset.sum_eq_single (lastIdx : Fin p)]
  · rw [val_lastIdx, coeff_pow_mul_eq_pow p _ _ (thetaL K T) (coeff_pow_pred_mul_thetaL p T) n]
  · intro i _ hi
    have hz : ∀ m : ℤ, (T ^ (i : ℕ) * thetaL K T).coeff (m * p) =
        ((0 : LaurentSeries K).coeff m) ^ p := fun m => by
      rw [HahnSeries.coeff_zero, zero_pow hp.out.ne_zero,
        coeff_pow_mul_thetaL_eq_zero p T (natCast_succ_ne_zero (F := K) hi) m]
    rw [coeff_pow_mul_eq_pow p _ _ 0 hz n, mul_zero, HahnSeries.coeff_zero,
      zero_pow hp.out.ne_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end CartierQExp

section QExpInj

variable {K : Type*} [Field K]

theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have hc := congrArg (fun s : LaurentSeries K => s.coeff (-1 : ℤ)) h
  beta_reduce at hc
  rw [thetaL_apply, theta_coeff, coeff_jqModC_neg_one, HahnSeries.coeff_zero, zsmul_eq_mul,
    mul_one, Int.cast_neg, Int.cast_one, neg_eq_zero] at hc
  exact one_ne_zero hc

variable {F : Type*} [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)

theorem D_ne_zero_of_thetaL_ne_zero (y : F) (hy : thetaL K (ι y) ≠ 0) :
    KaehlerDifferential.D K F y ≠ 0 := by
  intro h0
  apply hy
  rw [← qExpansionDiffAlong_D ι y, h0, map_zero]

theorem exists_smul_D_eq [AlgebraicCurve.IsCurveOver K F] (y : F) (hy : thetaL K (ι y) ≠ 0)
    (ω : Ω[F⁄K]) : ∃ f : F, f • KaehlerDifferential.D K F y = ω :=
  (finrank_eq_one_iff_of_nonzero' (KaehlerDifferential.D K F y)
    (D_ne_zero_of_thetaL_ne_zero ι y hy)).mp AlgebraicCurve.IsCurveOver.finrank_kaehler ω

theorem qexp_injective [AlgebraicCurve.IsCurveOver K F] (y : F) (hy : thetaL K (ι y) ≠ 0) :
    Function.Injective (qExpansionDiffAlong ι) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨g, rfl⟩ := exists_smul_D_eq ι y hy ω
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D] at hω
  rcases mul_eq_zero.mp hω with hg | hθ
  · rw [(map_eq_zero ι).mp hg, zero_smul]
  · exact absurd hθ hy

end QExpInj

section Lift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  (Θ : Ω[F⁄K] →ₗ[K] LaurentSeries K) (hinj : Function.Injective Θ)

def liftAlong (T : LaurentSeries K →+ LaurentSeries K)
    (h : ∀ ω : Ω[F⁄K], ∃ ω' : Ω[F⁄K], Θ ω' = T (Θ ω)) : Ω[F⁄K] →+ Ω[F⁄K] where
  toFun ω := (h ω).choose
  map_zero' := hinj (by rw [(h 0).choose_spec, map_zero, map_zero])
  map_add' a b := hinj (by
    rw [(h (a + b)).choose_spec, map_add, map_add, map_add, (h a).choose_spec, (h b).choose_spec])

theorem apply_liftAlong (T : LaurentSeries K →+ LaurentSeries K)
    (h : ∀ ω : Ω[F⁄K], ∃ ω' : Ω[F⁄K], Θ ω' = T (Θ ω)) (ω : Ω[F⁄K]) :
    Θ (liftAlong Θ hinj T h ω) = T (Θ ω) :=
  (h ω).choose_spec

include hinj in
theorem liftAlong_eq_of (T : LaurentSeries K →+ LaurentSeries K)
    (h : ∀ ω : Ω[F⁄K], ∃ ω' : Ω[F⁄K], Θ ω' = T (Θ ω)) {ω ω' : Ω[F⁄K]}
    (e : Θ ω' = T (Θ ω)) : liftAlong Θ hinj T h ω = ω' :=
  hinj (by rw [apply_liftAlong, e])

def liftAlongLinear (T : LaurentSeries K →ₗ[K] LaurentSeries K)
    (h : ∀ ω : Ω[F⁄K], ∃ ω' : Ω[F⁄K], Θ ω' = T (Θ ω)) : Ω[F⁄K] →ₗ[K] Ω[F⁄K] :=
  { liftAlong Θ hinj T.toAddMonoidHom h with
    map_smul' := fun c ω => hinj (by
      show Θ (liftAlong Θ hinj T.toAddMonoidHom h (c • ω)) = Θ (c • liftAlong Θ hinj T.toAddMonoidHom h ω)
      rw [apply_liftAlong, Θ.map_smul c ω, Θ.map_smul c, apply_liftAlong]
      show T (c • Θ ω) = c • T (Θ ω)
      exact T.map_smul c (Θ ω)) }

theorem liftAlongLinear_apply (T : LaurentSeries K →ₗ[K] LaurentSeries K)
    (h : ∀ ω : Ω[F⁄K], ∃ ω' : Ω[F⁄K], Θ ω' = T (Θ ω)) (ω : Ω[F⁄K]) :
    liftAlongLinear Θ hinj T h ω = liftAlong Θ hinj T.toAddMonoidHom h ω := rfl

end Lift

section Frob

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
  (ι : F →ₐ[K] LaurentSeries K) (y : F)

theorem exists_qexp_eq_coeffMap (hy : thetaL K (ι y) ≠ 0) (τ : K →+* K) (g : SemilinearAut K F)
    (hg : ∀ f : F, ι (g • f) = coeffMap τ (ι f)) (ω : Ω[F⁄K]) :
    ∃ ω' : Ω[F⁄K], qExpansionDiffAlong ι ω' = coeffMap τ (qExpansionDiffAlong ι ω) := by
  obtain ⟨f, rfl⟩ := exists_smul_D_eq ι y hy ω
  refine ⟨(g • f) • KaehlerDifferential.D K F (g • y), ?_⟩
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D, qExpansionDiffAlong_smul,
    qExpansionDiffAlong_D, map_mul, hg, hg, thetaL_coeffMap]

variable (hy : thetaL K (ι y) ≠ 0) (τ : K →+* K) (g : SemilinearAut K F)
  (hg : ∀ f : F, ι (g • f) = coeffMap τ (ι f))

def frobDiff : Ω[F⁄K] →+ Ω[F⁄K] :=
  liftAlong (qExpansionDiffAlong ι) (qexp_injective ι y hy) (coeffMap τ).toAddMonoidHom
    (exists_qexp_eq_coeffMap ι y hy τ g hg)

theorem qexp_frobDiff (ω : Ω[F⁄K]) :
    qExpansionDiffAlong ι (frobDiff ι y hy τ g hg ω) = coeffMap τ (qExpansionDiffAlong ι ω) :=
  apply_liftAlong _ _ _ _ ω

theorem frobDiff_eq_of {ω ω' : Ω[F⁄K]}
    (e : qExpansionDiffAlong ι ω' = coeffMap τ (qExpansionDiffAlong ι ω)) :
    frobDiff ι y hy τ g hg ω = ω' :=
  liftAlong_eq_of _ (qexp_injective ι y hy) _ _ e

include hg in

theorem frobDiff_smul_D (f h : F) :
    frobDiff ι y hy τ g hg (f • KaehlerDifferential.D K F h) =
      (g • f) • KaehlerDifferential.D K F (g • h) := by
  refine frobDiff_eq_of ι y hy τ g hg ?_
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D, qExpansionDiffAlong_smul,
    qExpansionDiffAlong_D, map_mul, hg, hg, thetaL_coeffMap]

theorem frobDiff_smul (f : F) (ω : Ω[F⁄K]) :
    frobDiff ι y hy τ g hg (f • ω) = (g • f) • frobDiff ι y hy τ g hg ω := by
  refine frobDiff_eq_of ι y hy τ g hg ?_
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_smul, map_mul, hg, qexp_frobDiff]

theorem frobDiff_smul_base (c : K) (ω : Ω[F⁄K]) :
    frobDiff ι y hy τ g hg (c • ω) = (SemilinearAut.baseAut g c) • frobDiff ι y hy τ g hg ω := by
  rw [← algebraMap_smul F c ω, frobDiff_smul, SemilinearAut.smul_algebraMap, algebraMap_smul]

theorem frobDiff_frobDiff (τ' : K →+* K) (g' : SemilinearAut K F)
    (hg' : ∀ f : F, ι (g' • f) = coeffMap τ' (ι f)) (hττ' : τ'.comp τ = RingHom.id K)
    (ω : Ω[F⁄K]) :
    frobDiff ι y hy τ' g' hg' (frobDiff ι y hy τ g hg ω) = ω := by
  refine frobDiff_eq_of ι y hy τ' g' hg' ?_
  rw [qexp_frobDiff, coeffMap_coeffMap, hττ', coeffMap_id]

include hg in

theorem coe_inv_smul (τ' : K →+* K) (hττ' : τ'.comp τ = RingHom.id K) (f : F) :
    ι (g⁻¹ • f) = coeffMap τ' (ι f) := by
  conv_rhs => rw [← smul_inv_smul g f, hg]
  rw [coeffMap_coeffMap, hττ', coeffMap_id]

end Frob

section Regular

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_regularDifferentials_of_semilinear [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] (g : SemilinearAut K F) (Φ : Ω[F⁄K] →+ Ω[F⁄K])
    (hΦ : ∀ f h : F, Φ (f • KaehlerDifferential.D K F h) = (g • f) • KaehlerDifferential.D K F (g • h))
    {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) : Φ ω ∈ regularDifferentials K F := by
  intro w
  set v : Place K F := g⁻¹ • w with hv
  have hwv : w = g • v := by rw [hv, smul_inv_smul]
  obtain ⟨f, hf, hωf⟩ := hω v
  obtain ⟨π, hπ, hdc⟩ := v.exists_ord_eq_one_and_dCoord_eq
  obtain ⟨πw, hπw, hdcw⟩ := w.exists_ord_eq_one_and_dCoord_eq
  have hgπ : w.ord (g • π) = 1 := by rw [hwv, SemilinearAut.ord_smul, hπ]
  obtain ⟨u, hu0, hu⟩ :=
    AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver w πw (g • π) hπw hgπ
  have hgf : g • f ∈ w.toValuationSubring := by
    rw [hwv, SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g f _ hf
  have humem : u ∈ w.toValuationSubring := by
    by_cases hu' : u = 0
    · rw [hu']; exact w.toValuationSubring.zero_mem
    · exact (AlgebraicCurve.Place.mem_iff_ord_nonneg w hu').mpr hu0.ge
  refine ⟨g • f * u, mul_mem hgf humem, ?_⟩
  rw [hωf, hdc, hΦ, hu, hdcw, smul_smul]

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p] [CharP F p] [PerfectField K]
  [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]

theorem cartier_comm_of_semilinear (g : SemilinearAut K F) (Φ : Ω[F⁄K] →+ Ω[F⁄K])
    (hΦ : ∀ f h : F, Φ (f • KaehlerDifferential.D K F h) = (g • f) • KaehlerDifferential.D K F (g • h))
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0) (ω : Ω[F⁄K]) :
    C (Φ ω) = Φ (C ω) := by
  have hspan := kw_cart_hspan_of_isCurveOver hdt
  have hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x :=
    hsep_of_span_D_eq_top (K := K) (p := p) hspan
  have hdeg := kw_cart_minpoly_natDegree_eq (ℓ := p) hdt
  have hω := eq_sum_coordRoot_pow_smul t hdt hspan hsep hdeg ω
  have hC := apply_eq_coordRoot_last_smul C hsemi hker hlog t hdt hspan hsep hdeg ω
  set c := coordRoot t hdt hspan hsep hdeg ω with hc
  have hΦω : Φ ω = ∑ i : Fin p, (g • c i) ^ p •
      ((g • t) ^ (i : ℕ) • KaehlerDifferential.D K F (g • t)) := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hΦ, smul_mul', smul_pow', smul_pow', smul_smul]
  rw [hΦω, apply_sum_pow_smul C hsemi hker hlog, hC, hΦ]

end Regular

section Polar

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_polarDifferentials_of_semilinear [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] (g : SemilinearAut K F) (Φ : Ω[F⁄K] →+ Ω[F⁄K])
    (hΦ : ∀ f h : F, Φ (f • KaehlerDifferential.D K F h) = (g • f) • KaehlerDifferential.D K F (g • h))
    (S : Set (AlgebraicCurve.Place K F)) (hS : ∀ v : AlgebraicCurve.Place K F, v ∈ S ↔ g • v ∈ S)
    {ω : Ω[F⁄K]} (hω : ω ∈ AlgebraicCurve.polarDifferentials K F S) :
    Φ ω ∈ AlgebraicCurve.polarDifferentials K F S := by
  intro w
  set v : AlgebraicCurve.Place K F := g⁻¹ • w with hv
  have hwv : w = g • v := by rw [hv, smul_inv_smul]
  obtain ⟨π, hπ, hdc⟩ := v.exists_ord_eq_one_and_dCoord_eq
  obtain ⟨πw, hπw, hdcw⟩ := w.exists_ord_eq_one_and_dCoord_eq
  have hgπ : w.ord (g • π) = 1 := by rw [hwv, SemilinearAut.ord_smul, hπ]
  obtain ⟨u, hu0, hu⟩ :=
    AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver w πw (g • π) hπw hgπ
  have humem : u ∈ w.toValuationSubring := by
    by_cases hu' : u = 0
    · rw [hu']; exact w.toValuationSubring.zero_mem
    · exact (AlgebraicCurve.Place.mem_iff_ord_nonneg w hu').mpr hu0.ge
  have hunif : w.ord w.uniformizer = 1 :=
    w.ord_coe_irreducible (IsDiscreteValuationRing.exists_irreducible w.toValuationSubring).choose_spec
  have hunif0 : w.uniformizer ≠ 0 := fun h0 => by
    have h1 := hunif; rw [h0, AlgebraicCurve.Place.ord_zero] at h1; exact zero_ne_one h1
  constructor
  · intro hwS
    have hvS : v ∉ S := fun hvS => hwS (hwv ▸ (hS v).1 hvS)
    obtain ⟨f, hf, hωf⟩ := (hω v).1 hvS
    have hgf : g • f ∈ w.toValuationSubring := by
      rw [hwv, SemilinearAut.smul_toValuationSubring]
      exact ValuationSubring.smul_mem_pointwise_smul g f _ hf
    refine ⟨g • f * u, mul_mem hgf humem, ?_⟩
    rw [hωf, hdc, hΦ, hu, hdcw, smul_smul]
  · intro hwS
    have hvS : v ∈ S := (hS v).2 (hwv ▸ hwS)
    obtain ⟨f, hf, hωf⟩ := (hω v).2 hvS
    refine ⟨g • f * u, ?_, ?_⟩
    · by_cases hf0 : f = 0
      · rw [hf0, smul_zero, zero_mul, mul_zero]; exact w.toValuationSubring.zero_mem
      by_cases hu' : u = 0
      · rw [hu', mul_zero, mul_zero]; exact w.toValuationSubring.zero_mem
      have hvunif : v.ord v.uniformizer = 1 :=
        v.ord_coe_irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
      have hvunif0 : v.uniformizer ≠ 0 := fun h0 => by
        have h1 := hvunif; rw [h0, AlgebraicCurve.Place.ord_zero] at h1; exact zero_ne_one h1
      have hordf : -1 ≤ v.ord f := by
        have h1 := (AlgebraicCurve.Place.mem_iff_ord_nonneg v (mul_ne_zero hvunif0 hf0)).mp hf
        rw [AlgebraicCurve.Place.ord_mul v hvunif0 hf0, hvunif] at h1
        omega
      have hgf0 : g • f ≠ 0 := fun h0 => hf0 (by
        have h1 := congrArg (g⁻¹ • ·) h0; simpa using h1)
      rw [← mul_assoc]
      refine (AlgebraicCurve.Place.mem_iff_ord_nonneg w (mul_ne_zero (mul_ne_zero hunif0 hgf0) hu')).mpr ?_
      rw [AlgebraicCurve.Place.ord_mul w (mul_ne_zero hunif0 hgf0) hu', AlgebraicCurve.Place.ord_mul w hunif0 hgf0,
        hunif, hu0, hwv, SemilinearAut.ord_smul]
      omega
    · rw [hωf, hdc, hΦ, hu, hdcw, smul_smul]

end Polar

section Endgame

variable {K : Type*} [Field K] {Ω : Type*} [AddCommGroup Ω] [Module K Ω]

theorem map_mem_span_image (T : Ω →+ Ω) (τ : K → K)
    (hT : ∀ (c : K) (ω : Ω), T (c • ω) = τ c • T ω)
    {S : Set Ω} {ω : Ω} (hω : ω ∈ Submodule.span K S) : T ω ∈ Submodule.span K (T '' S) := by
  induction hω using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [hT]; exact Submodule.smul_mem _ _ hx

variable [IsAlgClosed K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

theorem le_span_fixed_of_surjOn (R : Submodule K Ω) [FiniteDimensional K R]
    (C : Ω →+ Ω) (hC : ∀ (c : K) (ω : Ω), C (c ^ p • ω) = c • C ω)
    (Φ Ψ : Ω →+ Ω) (hΦ : ∀ (c : K) (ω : Ω), Φ (c • ω) = c ^ p • Φ ω)
    (hΨΦ : ∀ ω, Ψ (Φ ω) = ω) (hΦΨ : ∀ ω, Φ (Ψ ω) = ω)
    (hΦR : ∀ ω ∈ R, Φ ω ∈ R) (hΨR : ∀ ω ∈ R, Ψ ω ∈ R)
    (hcomm : ∀ ω, C (Φ ω) = Φ (C ω))
    (𝒞 : Ω →ₗ[K] Ω) (h𝒞 : ∀ ω, 𝒞 ω = Φ (C ω))
    (W : Submodule K Ω) (hWR : W ≤ R) (hWC : ∀ w' ∈ W, ∃ w ∈ W, w' = 𝒞 w) :
    W ≤ Submodule.span K {ω : Ω | ω ∈ R ∧ C ω = ω} := by
  haveI := PerfectField.toPerfectRing (K := K) p
  set ρ : K → K := fun c => (frobeniusEquiv K p).symm c with hρ
  have hρp : ∀ c : K, ρ c ^ p = c := fun c => frobeniusEquiv_symm_pow_p K p c

  have hΦinj : Function.Injective Φ := fun a b h => by rw [← hΨΦ a, ← hΨΦ b, h]
  have hCs : ∀ (c : K) (ω : Ω), C (c • ω) = ρ c • C ω := fun c ω => by
    conv_lhs => rw [← hρp c]
    exact hC _ _
  have hΨs : ∀ (c : K) (ω : Ω), Ψ (c • ω) = ρ c • Ψ ω := fun c ω =>
    hΦinj (by rw [hΦΨ, hΦ, hρp, hΦΨ])
  have hcommΨ : ∀ ω, C (Ψ ω) = Ψ (C ω) := fun ω =>
    hΦinj (by rw [← hcomm, hΦΨ, hΦΨ])
  have h𝒞Φ : Function.Commute 𝒞 Φ := fun ω => by
    show 𝒞 (Φ ω) = Φ (𝒞 ω)
    rw [h𝒞, h𝒞, hcomm]
  have h𝒞Ψ : Function.Commute 𝒞 Ψ := fun ω => by
    show 𝒞 (Ψ ω) = Ψ (𝒞 ω)
    rw [h𝒞, h𝒞, hcommΨ, hΦΨ, hΨΦ]
  have hCΦ : Function.Commute C Φ := fun ω => hcomm ω
  have hCΨ : Function.Commute C Ψ := fun ω => hcommΨ ω
  have hΨ𝒞 : ∀ ω, Ψ (𝒞 ω) = C ω := fun ω => by rw [h𝒞, hΨΦ]
  have hΦiR : ∀ (n : ℕ), ∀ ω ∈ R, Φ^[n] ω ∈ R := by
    intro n
    induction n with
    | zero => intro ω hω; exact hω
    | succ n ih => intro ω hω; rw [Function.iterate_succ_apply']; exact hΦR _ (ih ω hω)
  have hΨiR : ∀ (n : ℕ), ∀ ω ∈ R, Ψ^[n] ω ∈ R := by
    intro n
    induction n with
    | zero => intro ω hω; exact hω
    | succ n ih => intro ω hω; rw [Function.iterate_succ_apply']; exact hΨR _ (ih ω hω)

  haveI : FiniteDimensional K W := Submodule.finiteDimensional_of_le hWR
  have hWle : W ≤ W.map 𝒞 := fun w hw => by
    obtain ⟨w₁, hw₁, rfl⟩ := hWC w hw
    exact Submodule.mem_map_of_mem hw₁
  have hWeq : W = W.map 𝒞 :=
    Submodule.eq_of_le_of_finrank_le hWle (Submodule.finrank_map_le 𝒞 W)
  have h𝒞W : ∀ w ∈ W, 𝒞 w ∈ W := fun w hw => by
    rw [hWeq]; exact Submodule.mem_map_of_mem hw
  have hW𝒞 : ∀ w ∈ W, ∃ w₁ ∈ W, 𝒞 w₁ = w := fun w hw => by
    obtain ⟨w₁, hw₁, e⟩ := hWC w hw
    exact ⟨w₁, hw₁, e.symm⟩

  set U : Set Ω := {ω | ∃ n : ℕ, ∃ w ∈ W, ω = Φ^[n] w ∨ ω = Ψ^[n] w} with hU
  have hWU : (W : Set Ω) ⊆ U := fun w hw => ⟨0, w, hw, Or.inl rfl⟩
  have hUR : U ⊆ R := by
    rintro ω ⟨n, w, hw, h | h⟩ <;> rw [h]
    · exact hΦiR n w (hWR hw)
    · exact hΨiR n w (hWR hw)
  have hΦU : Φ '' U ⊆ U := by
    rintro _ ⟨ω, ⟨n, w, hw, h | h⟩, rfl⟩ <;> rw [h]
    · exact ⟨n + 1, w, hw, Or.inl (Function.iterate_succ_apply' Φ n w).symm⟩
    · cases n with
      | zero => exact ⟨1, w, hw, Or.inl rfl⟩
      | succ m => exact ⟨m, w, hw, Or.inr (by rw [Function.iterate_succ_apply', hΦΨ])⟩
  have hΨU : Ψ '' U ⊆ U := by
    rintro _ ⟨ω, ⟨n, w, hw, h | h⟩, rfl⟩ <;> rw [h]
    · cases n with
      | zero => exact ⟨1, w, hw, Or.inr rfl⟩
      | succ m => exact ⟨m, w, hw, Or.inl (by rw [Function.iterate_succ_apply', hΨΦ])⟩
    · exact ⟨n + 1, w, hw, Or.inr (Function.iterate_succ_apply' Ψ n w).symm⟩
  have h𝒞U : 𝒞 '' U ⊆ U := by
    rintro _ ⟨ω, ⟨n, w, hw, h | h⟩, rfl⟩ <;> rw [h]
    · exact ⟨n, 𝒞 w, h𝒞W w hw, Or.inl (h𝒞Φ.iterate_right n w)⟩
    · exact ⟨n, 𝒞 w, h𝒞W w hw, Or.inr (h𝒞Ψ.iterate_right n w)⟩
  have hU𝒞 : U ⊆ 𝒞 '' U := by
    rintro ω ⟨n, w, hw, h | h⟩ <;> obtain ⟨w₁, hw₁, rfl⟩ := hW𝒞 w hw <;> rw [h]
    · exact ⟨Φ^[n] w₁, ⟨n, w₁, hw₁, Or.inl rfl⟩, h𝒞Φ.iterate_right n w₁⟩
    · exact ⟨Ψ^[n] w₁, ⟨n, w₁, hw₁, Or.inr rfl⟩, h𝒞Ψ.iterate_right n w₁⟩
  have hCU : C '' U ⊆ U := by
    rintro _ ⟨ω, ⟨n, w, hw, h | h⟩, rfl⟩ <;> rw [h]
    · rw [hCΦ.iterate_right n w, ← hΨ𝒞]
      cases n with
      | zero => exact ⟨1, 𝒞 w, h𝒞W w hw, Or.inr rfl⟩
      | succ m =>
        exact ⟨m, 𝒞 w, h𝒞W w hw, Or.inl (by rw [Function.iterate_succ_apply, hΦΨ])⟩
    · rw [hCΨ.iterate_right n w, ← hΨ𝒞]
      exact ⟨n + 1, 𝒞 w, h𝒞W w hw, Or.inr (Function.iterate_succ_apply Ψ n (𝒞 w)).symm⟩
  set V : Submodule K Ω := Submodule.span K U with hV
  have hVR : V ≤ R := Submodule.span_le.mpr hUR
  haveI : FiniteDimensional K V := Submodule.finiteDimensional_of_le hVR
  have hWV : W ≤ V := fun w hw => Submodule.subset_span (hWU hw)
  have hΦV : ∀ v ∈ V, Φ v ∈ V := fun v hv =>
    Submodule.span_mono hΦU (map_mem_span_image Φ (fun c => c ^ p) hΦ hv)
  have hΨV : ∀ v ∈ V, Ψ v ∈ V := fun v hv =>
    Submodule.span_mono hΨU (map_mem_span_image Ψ ρ hΨs hv)
  have hCV : ∀ v ∈ V, C v ∈ V := fun v hv =>
    Submodule.span_mono hCU (map_mem_span_image C ρ hCs hv)
  have h𝒞V : ∀ v ∈ V, 𝒞 v ∈ V := fun v hv =>
    Submodule.span_mono h𝒞U
      (map_mem_span_image 𝒞.toAddMonoidHom id (fun c ω => 𝒞.map_smul c ω) hv)

  have hVle : V ≤ V.map 𝒞 := by
    rw [hV, ← Submodule.span_image]
    exact Submodule.span_mono hU𝒞
  set 𝒞V : V →ₗ[K] V := 𝒞.restrict h𝒞V with h𝒞Vdef
  have h𝒞Vsurj : Function.Surjective 𝒞V := by
    intro ⟨v, hv⟩
    obtain ⟨u, hu, e⟩ := Submodule.mem_map.mp (hVle hv)
    exact ⟨⟨u, hu⟩, Subtype.ext e⟩
  have h𝒞Vinj : Function.Injective 𝒞V := LinearMap.injective_iff_surjective.mpr h𝒞Vsurj
  have h𝒞inj : ∀ v ∈ V, 𝒞 v = 0 → v = 0 := fun v hv h0 => by
    have : 𝒞V ⟨v, hv⟩ = 𝒞V 0 := Subtype.ext (by simpa [h𝒞Vdef] using h0)
    exact congrArg Subtype.val (h𝒞Vinj this)

  set CV : V →+ V :=
    { toFun := fun v => ⟨C (v : Ω), hCV (v : Ω) v.2⟩
      map_zero' := Subtype.ext (by
        show C ((0 : V) : Ω) = ((0 : V) : Ω)
        rw [Submodule.coe_zero, map_zero])
      map_add' := fun a b => Subtype.ext (by
        show C ((a + b : V) : Ω) = C (a : Ω) + C (b : Ω)
        rw [Submodule.coe_add, map_add]) } with hCVdef
  have hCVapply : ∀ v : V, ((CV v : V) : Ω) = C (v : Ω) := fun v => rfl
  have hCVinj : Function.Injective CV := by
    intro a b h
    have h' : C (a : Ω) = C b := congrArg Subtype.val h
    have hab : (a : Ω) - b = 0 := by
      refine h𝒞inj _ (V.sub_mem a.2 b.2) ?_
      rw [h𝒞, map_sub, h', sub_self, map_zero]
    exact Subtype.ext (sub_eq_zero.mp hab)
  have hCVsurj : Function.Surjective CV := by
    intro ⟨v, hv⟩
    obtain ⟨⟨u, hu⟩, e⟩ := h𝒞Vsurj ⟨Φ v, hΦV v hv⟩
    have e' : 𝒞 u = Φ v := congrArg Subtype.val e
    refine ⟨⟨u, hu⟩, Subtype.ext (hΦinj ?_)⟩
    rw [hCVapply, ← h𝒞, e']
  set θ : V →+ V := (AddEquiv.ofBijective CV ⟨hCVinj, hCVsurj⟩).symm.toAddMonoidHom with hθ
  have hCθ : ∀ v : V, CV (θ v) = v := fun v =>
    (AddEquiv.ofBijective CV ⟨hCVinj, hCVsurj⟩).apply_symm_apply v
  have hθC : ∀ v : V, θ (CV v) = v := fun v =>
    (AddEquiv.ofBijective CV ⟨hCVinj, hCVsurj⟩).symm_apply_apply v
  have hθsemi : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ 1 • θ v := fun c v => by
    apply hCVinj
    rw [hCθ, pow_one]
    refine Subtype.ext ?_
    rw [hCVapply, Submodule.coe_smul, Submodule.coe_smul, hC, ← hCVapply, hCθ]
  have hθinj : Function.Injective θ :=
    (AddEquiv.ofBijective CV ⟨hCVinj, hCVsurj⟩).symm.injective

  have hLS := Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
    (K := K) (V := V) (p := p) 1 one_ne_zero θ hθsemi hθinj

  intro w hw
  have hwV : (⟨w, hWV hw⟩ : V) ∈ Submodule.span K (Function.fixedPoints θ) := by
    rw [hLS]; exact Submodule.mem_top
  have hmap : w ∈ Submodule.span K (V.subtype '' Function.fixedPoints θ) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map_of_mem hwV
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨v, hv, rfl⟩
  have hfix : θ v = v := hv
  have hCv : CV v = v := by rw [← hfix, hCθ, hfix]
  exact ⟨hVR v.2, by show C (v : Ω) = (v : Ω); rw [← hCVapply, hCv]⟩

end Endgame

section Assembly

open scoped MatrixGroups

variable (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

theorem val_apply (x : qExpFunctionFieldC K Γ) :
    (qExpFunctionFieldC K Γ).val x = (x : LaurentSeries K) := rfl

theorem le_span_logarithmic_polar (hT : ModularGroup.T ∈ Γ)
    (W : Submodule K Ω[qExpFunctionFieldC K Γ⁄K])
    (hWreg : W ≤ ssPolarDifferentials K Γ p)
    (hWC : ∀ w' ∈ W, ∃ w ∈ W, w' = frobPushDiffModL K Γ p w) :
    W ≤ Submodule.span K {ω : Ω[qExpFunctionFieldC K Γ⁄K] |
      ω ∈ ssPolarDifferentials K Γ p ∧
        ∃ f : qExpFunctionFieldC K Γ, f ≠ 0 ∧
          ω = f⁻¹ • KaehlerDifferential.D K (qExpFunctionFieldC K Γ) f} := by

  obtain ⟨x, hxj, hxt, hxfd⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI := hxfd
  haveI hcurve : AlgebraicCurve.IsCurveOver K (qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hxfd
  haveI hft : Algebra.EssFiniteType K (qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  haveI : CharP (qExpFunctionFieldC K Γ) p :=
    charP_of_injective_algebraMap (algebraMap K (qExpFunctionFieldC K Γ)).injective p
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(qExpFunctionFieldC K Γ)) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

  have hSSfin : (ssPlacesQExp K Γ p).Finite := finite_ssPlacesQExp K p Γ hT
  haveI : FiniteDimensional K (ssPolarDifferentials K Γ p) := by
    obtain ⟨-, -, -, -, -, hfin, -⟩ :=
      AlgebraicCurve.exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
        (K := K) (F := ↥(qExpFunctionFieldC K Γ)) hSSfin.toFinset
    have hset : ((hSSfin.toFinset : Finset _) : Set (AlgebraicCurve.Place K (qExpFunctionFieldC K Γ))) =
        ssPlacesQExp K Γ p := hSSfin.coe_toFinset
    have hsub : AlgebraicCurve.polarDifferentials K (qExpFunctionFieldC K Γ)
        ((hSSfin.toFinset : Finset _) : Set (AlgebraicCurve.Place K (qExpFunctionFieldC K Γ))) =
        ssPolarDifferentials K Γ p := by
      rw [hset]; rfl
    rw [← hsub]; exact hfin
  haveI := PerfectField.toPerfectRing (K := K) p
  set ι : qExpFunctionFieldC K Γ →ₐ[K] LaurentSeries K := (qExpFunctionFieldC K Γ).val with hι

  have hιx : ι x = jqModC K := hxj
  have hy : thetaL K (ι x) ≠ 0 := by rw [hιx]; exact thetaL_jqModC_ne_zero
  have hdx : KaehlerDifferential.D K (qExpFunctionFieldC K Γ) x ≠ 0 :=
    D_ne_zero_of_thetaL_ne_zero ι x hy
  have hinj := qexp_injective ι x hy

  obtain ⟨C, ⟨hsemi, hker, hlog⟩, -⟩ :=
    AlgebraicCurve.cartierOperator_existsUnique (K := K) (F := ↥(qExpFunctionFieldC K Γ)) p x

  set σ : SemilinearAut K (qExpFunctionFieldC K Γ) := qExpArithFrobC p K Γ with hσ
  set Fr : K →+* K := frobenius K p with hFr
  set Fr' : K →+* K := ((frobeniusEquiv K p).symm : K →+* K) with hFr'
  have hFF : Fr'.comp Fr = RingHom.id K := frobeniusEquiv_symm_comp_frobenius K p
  have hFF' : Fr.comp Fr' = RingHom.id K := frobenius_comp_frobeniusEquiv_symm K p
  have hσc : ∀ f : qExpFunctionFieldC K Γ, ι (σ • f) = coeffMap Fr (ι f) := fun f => rfl
  have hσc' : ∀ f : qExpFunctionFieldC K Γ, ι (σ⁻¹ • f) = coeffMap Fr' (ι f) :=
    coe_inv_smul ι Fr σ hσc Fr' hFF
  set Φ := frobDiff ι x hy Fr σ hσc with hΦ
  set Ψ := frobDiff ι x hy Fr' σ⁻¹ hσc' with hΨ
  have hΦD := frobDiff_smul_D ι x hy Fr σ hσc
  have hΨD := frobDiff_smul_D ι x hy Fr' σ⁻¹ hσc'
  have hΨΦ : ∀ ω, Ψ (Φ ω) = ω := frobDiff_frobDiff ι x hy Fr σ hσc Fr' σ⁻¹ hσc' hFF
  have hΦΨ : ∀ ω, Φ (Ψ ω) = ω := frobDiff_frobDiff ι x hy Fr' σ⁻¹ hσc' Fr σ hσc hFF'
  have hΦK : ∀ (c : K) (ω : Ω[qExpFunctionFieldC K Γ⁄K]), Φ (c • ω) = c ^ p • Φ ω := fun c ω => by
    rw [hΦ, frobDiff_smul_base]
    exact congrArg (· • frobDiff ι x hy Fr σ hσc ω) (baseAut_qExpArithFrobC_apply p K Γ c)

  have hSSfwd : ∀ (g : SemilinearAut K (qExpFunctionFieldC K Γ)),
      (∀ z : qExpFunctionFieldC K Γ, ι z = jqModC K → ι (g • z) = jqModC K) →
      (∀ a : K, a ∈ @ssJSet p K _ (Classical.decEq K) → SemilinearAut.baseAut g a ∈ @ssJSet p K _ (Classical.decEq K)) →
      ∀ v : AlgebraicCurve.Place K (qExpFunctionFieldC K Γ), v ∈ ssPlacesQExp K Γ p → g • v ∈ ssPlacesQExp K Γ p := by
    intro g hgj hga v hv
    obtain ⟨z, a, hz, hva, ha⟩ := hv
    exact ⟨g • z, SemilinearAut.baseAut g a, hgj z hz, hva.smul g, hga a ha⟩
  have hσj : ∀ z : qExpFunctionFieldC K Γ, ι z = jqModC K → ι (σ • z) = jqModC K := fun z hz => by
    rw [hσc, hz, coeffMap_jqModC]
  have hσ'j : ∀ z : qExpFunctionFieldC K Γ, ι z = jqModC K → ι (σ⁻¹ • z) = jqModC K := fun z hz => by
    rw [hσc', hz, coeffMap_jqModC]
  have hσa : ∀ a : K, a ∈ @ssJSet p K _ (Classical.decEq K) →
      SemilinearAut.baseAut σ a ∈ @ssJSet p K _ (Classical.decEq K) := fun a ha => by
    rw [show SemilinearAut.baseAut σ a = a ^ p from baseAut_qExpArithFrobC_apply p K Γ a]
    exact (@pow_mem_ssJSet_iff_of_perfectField K _ (Classical.decEq K) p _ _ _ a).2 ha
  have hσ'a : ∀ a : K, a ∈ @ssJSet p K _ (Classical.decEq K) →
      SemilinearAut.baseAut σ⁻¹ a ∈ @ssJSet p K _ (Classical.decEq K) := fun a ha => by
    have hb : (SemilinearAut.baseAut σ⁻¹ a) ^ p = a := by
      rw [← baseAut_qExpArithFrobC_apply p K Γ, ← hσ]
      show SemilinearAut.baseAut σ (SemilinearAut.baseAut σ⁻¹ a) = a
      rw [SemilinearAut.baseAut_inv]; exact RingEquiv.apply_symm_apply _ _
    exact (@pow_mem_ssJSet_iff_of_perfectField K _ (Classical.decEq K) p _ _ _ _).1 (hb.symm ▸ ha)
  have hSσ : ∀ v : AlgebraicCurve.Place K (qExpFunctionFieldC K Γ), v ∈ ssPlacesQExp K Γ p ↔ σ • v ∈ ssPlacesQExp K Γ p :=
    fun v => ⟨hSSfwd σ hσj hσa v, fun h => by simpa using hSSfwd σ⁻¹ hσ'j hσ'a _ h⟩
  have hSσ' : ∀ v : AlgebraicCurve.Place K (qExpFunctionFieldC K Γ), v ∈ ssPlacesQExp K Γ p ↔ σ⁻¹ • v ∈ ssPlacesQExp K Γ p :=
    fun v => ⟨hSSfwd σ⁻¹ hσ'j hσ'a v, fun h => by simpa using hSSfwd σ hσj hσa _ h⟩
  have hΦR : ∀ ω ∈ ssPolarDifferentials K Γ p, Φ ω ∈ ssPolarDifferentials K Γ p := fun ω hω =>
    mem_polarDifferentials_of_semilinear σ Φ hΦD (ssPlacesQExp K Γ p) hSσ hω
  have hΨR : ∀ ω ∈ ssPolarDifferentials K Γ p, Ψ ω ∈ ssPolarDifferentials K Γ p := fun ω hω =>
    mem_polarDifferentials_of_semilinear σ⁻¹ Ψ hΨD (ssPlacesQExp K Γ p) hSσ' hω
  have hcomm : ∀ ω, C (Φ ω) = Φ (C ω) :=
    cartier_comm_of_semilinear σ Φ hΦD C hsemi hker hlog x hdx

  have hcart : ∀ (ω : Ω[qExpFunctionFieldC K Γ⁄K]) (m : ℤ),
      (qExpansionDiffAlong ι ω).coeff (m * p) = ((qExpansionDiffAlong ι (C ω)).coeff m) ^ p :=
    fun ω m => (coeff_qexp_cartier_pow p hft x hdx ι C hsemi hker hlog ω m).symm
  have hdec : ∀ ω : Ω[qExpFunctionFieldC K Γ⁄K],
      qExpansionDiffAlong ι (Φ (C ω)) = qDecimate K p (qExpansionDiffAlong ι ω) := fun ω => by
    rw [hΦ, qexp_frobDiff, qDecimate_eq_coeffMap_frobenius p (hcart ω)]
  have hex : ∀ ω : Ω[qExpFunctionFieldC K Γ⁄K], ∃ ω',
      qExpansionDiffAlong ι ω' = qDecimate K p (qExpansionDiffAlong ι ω) :=
    fun ω => ⟨Φ (C ω), hdec ω⟩
  set 𝒞₀ := liftAlongLinear (qExpansionDiffAlong ι) hinj (qDecimate K p) hex with h𝒞₀
  have h𝒞₀ : ∀ ω, 𝒞₀ ω = Φ (C ω) := fun ω =>
    liftAlong_eq_of _ hinj _ hex (hdec ω)
  have hΘ : ∀ ω : Ω[qExpFunctionFieldC K Γ⁄K],
      qExpansionDiffAlong ι ω = diffQExp (qExpFunctionFieldC K Γ) ω :=
    qExpansionDiffAlong_val_eq_diffQExp (qExpFunctionFieldC K Γ)
  have hpin₀ : IsFrobPushDiff K Γ p 𝒞₀ := fun ω => by
    rw [← hΘ, ← hΘ, h𝒞₀, hdec]
  have hpin : IsFrobPushDiff K Γ p (frobPushDiffModL K Γ p) :=
    isFrobPushDiff_frobPushDiffModL ⟨𝒞₀, hpin₀⟩
  have h𝒞 : ∀ ω, frobPushDiffModL K Γ p ω = Φ (C ω) := fun ω => by
    apply hinj
    rw [hΘ, hpin ω, ← hΘ, hdec]

  have hCK : ∀ (c : K) (ω : Ω[qExpFunctionFieldC K Γ⁄K]), C (c ^ p • ω) = c • C ω := fun c ω => by
    rw [← algebraMap_smul (qExpFunctionFieldC K Γ) (c ^ p) ω, map_pow, hsemi, algebraMap_smul]

  have hmain := le_span_fixed_of_surjOn (p := p) (ssPolarDifferentials K Γ p)
    C hCK Φ Ψ hΦK hΨΦ hΦΨ hΦR hΨR hcomm (frobPushDiffModL K Γ p) h𝒞 W hWreg hWC
  refine hmain.trans (Submodule.span_mono ?_)
  rintro ω ⟨hωR, hfix⟩
  exact ⟨hωR, AlgebraicCurve.exists_dlog_of_cartierOperator_fixed p x C hsemi hker hlog ω hfix⟩

end Assembly

end LogSpan

end

open scoped MatrixGroups in
open LogSpan in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (W : Submodule K ↥(ModularCurve.ssPolarDifferentials K Γ p))

    (hWC : ∀ w' ∈ W, ∃ w ∈ W,
      ((w' : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) =
        ModularCurve.frobPushDiffModL K Γ p ((w : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])) :
    W ≤ Submodule.span K {η : ↥(ModularCurve.ssPolarDifferentials K Γ p) |
        ∃ f : ModularCurve.qExpFunctionFieldC K Γ, f ≠ 0 ∧
          ((η : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) =
            f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K Γ) f} := by

  set W' : Submodule K Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] :=
    W.map (ModularCurve.ssPolarDifferentials K Γ p).subtype with hW'
  have hW'reg : W' ≤ ModularCurve.ssPolarDifferentials K Γ p := by
    rintro _ ⟨w, hw, rfl⟩
    exact w.2
  have hW'C : ∀ w' ∈ W', ∃ w ∈ W', w' = ModularCurve.frobPushDiffModL K Γ p w := by
    rintro _ ⟨w', hw', rfl⟩
    obtain ⟨w, hw, e⟩ := hWC w' hw'
    exact ⟨(w : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]), ⟨w, hw, rfl⟩, e⟩
  have hmain := le_span_logarithmic_polar K p Γ hT W' hW'reg hW'C

  intro w hw
  have hw' : (w : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) ∈ W' := ⟨w, hw, rfl⟩
  have hmem := hmain hw'
  have himage : {ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] |
      ω ∈ ModularCurve.ssPolarDifferentials K Γ p ∧
        ∃ f : ModularCurve.qExpFunctionFieldC K Γ, f ≠ 0 ∧
          ω = f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K Γ) f} ⊆
      (ModularCurve.ssPolarDifferentials K Γ p).subtype ''
        {η : ↥(ModularCurve.ssPolarDifferentials K Γ p) |
          ∃ f : ModularCurve.qExpFunctionFieldC K Γ, f ≠ 0 ∧
            ((η : ↥(ModularCurve.ssPolarDifferentials K Γ p)) : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) =
              f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K Γ) f} := by
    rintro ω ⟨hωR, hlog⟩
    exact ⟨⟨ω, hωR⟩, hlog, rfl⟩
  have hmem' := Submodule.span_mono himage hmem
  rw [Submodule.span_image] at hmem'
  obtain ⟨t, ht, e⟩ := Submodule.mem_map.mp hmem'
  have hteq : t = w := (ModularCurve.ssPolarDifferentials K Γ p).subtype_injective e
  rw [← hteq]
  exact ht

end S_ModularCurve_le_span_setOf_logarithmic_of_frobPushDiffModL_surjOn
end P2MW
export P2MW.S_ModularCurve_le_span_setOf_logarithmic_of_frobPushDiffModL_surjOn (solution)
