-- Prove2me | solution 1 for ModularCurve.ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e8206593-cb0a-5603-b727-19a75246088e

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

namespace CDivJ
namespace TameOrder

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap_eq_zero (w : Place K F) {c : K} (hc : c ≠ 0) :
    w.ord (algebraMap K F c) = 0 := by
  have hne : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have h1 : 0 ≤ w.ord (algebraMap K F c) :=
    (Place.mem_iff_ord_nonneg _ hne).mp (w.algebraMap_mem' c)
  have h2 : 0 ≤ w.ord (algebraMap K F c)⁻¹ := by
    rw [show (algebraMap K F c)⁻¹ = algebraMap K F c⁻¹ from (map_inv₀ _ c).symm]
    exact (Place.mem_iff_ord_nonneg _ ((map_ne_zero _).mpr (inv_ne_zero hc))).mp
      (w.algebraMap_mem' c⁻¹)
  rw [Place.ord_inv] at h2
  omega

theorem diffCoeff_eq_of_eq_smul {t : F} (hDt : D K F t ≠ 0) {ω : Ω[F⁄K]} {g : F}
    (h : ω = g • D K F t) : Place.diffCoeff t ω = g := by
  have h1 : Place.diffCoeff t ω • D K F t = ω := Place.diffCoeff_smul_D ⟨g, h⟩
  have h2 : (Place.diffCoeff t ω - g) • D K F t = 0 := by
    rw [sub_smul, h1, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hDt

variable [PerfectField K]

theorem exists_good_coeff (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ))
    (he : ((e : ℕ) : K) ≠ 0) :
    ∃ g₀ : F, g₀ ≠ 0 ∧ D K F s = g₀ • D K F w.uniformizer_alt ∧ w.ord g₀ = (e : ℤ) - 1 := by
  classical
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hords
    omega
  set u := w.uniformizer_alt with hudef
  have hu1 : w.ord u = 1 := w.ord_uniformizer_alt w.exists_ord_eq_one
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hu1
    exact one_ne_zero hu1.symm
  have hupow : u ^ (e : ℕ) ≠ 0 := pow_ne_zero _ hune
  have hordupow : w.ord (u ^ (e : ℕ)) = (e : ℤ) := by
    rw [show u ^ (e : ℕ) = u ^ ((e : ℕ) : ℤ) from (zpow_natCast u e).symm,
      Place.ord_zpow, hu1, mul_one]
  set c : F := s / u ^ (e : ℕ) with hcdef
  have hcne : c ≠ 0 := div_ne_zero hsne hupow
  have hordc : w.ord c = 0 := by
    rw [hcdef, div_eq_mul_inv, w.ord_mul hsne (inv_ne_zero hupow), Place.ord_inv,
      hordupow, hords]
    ring
  have hs_eq : s = c * u ^ (e : ℕ) := (div_mul_cancel₀ s hupow).symm
  have heF : ((e : ℕ) : F) ≠ 0 := by
    rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact (map_ne_zero _).mpr he
  have hordeF : w.ord ((e : ℕ) : F) = 0 := by
    rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact ord_algebraMap_eq_zero w he
  have htr : Transcendental K u := w.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({u} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x w hu1
  have hDu : D K F u ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K u htr
  set cv := Place.diffCoeff u (D K F c) with hcvdef
  have hDc : D K F c = cv • D K F u :=
    (Place.diffCoeff_smul_D
      ((KaehlerDifferential.exists_unique_smul_D_of_transcendental K u htr (D K F c)).exists)).symm
  have hcv0 : 0 ≤ w.ord cv :=
    Place.ord_diffCoeff_D_nonneg_of_isSeparable x w hu1 (le_of_eq hordc.symm)
  have hD : D K F s = (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv) • D K F u := by
    conv_lhs => rw [hs_eq]
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDc]
    rw [← Nat.cast_smul_eq_nsmul F e (u ^ ((e : ℕ) - 1) • D K F u)]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
  have hmne : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcne heF) (pow_ne_zero _ hune)
  have hordmain : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1)) = (e : ℤ) - 1 := by
    rw [w.ord_mul (mul_ne_zero hcne heF) (pow_ne_zero _ hune),
      w.ord_mul hcne heF, hordc, hordeF,
      show u ^ ((e : ℕ) - 1) = u ^ (((e : ℕ) - 1 : ℕ) : ℤ) from (zpow_natCast u _).symm,
      Place.ord_zpow, hu1, mul_one]
    have : (((e : ℕ) - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    omega
  refine ⟨c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv, ?_, hD, ?_⟩
  · by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero]
      exact hmne
    · intro h0
      have h1 : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) = -(u ^ (e : ℕ) * cv) := by
        linear_combination h0
      have h2 : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1))
          = w.ord (u ^ (e : ℕ) * cv) := by
        rw [h1, show -(u ^ (e : ℕ) * cv) = (-1 : F) * (u ^ (e : ℕ) * cv) by ring,
          w.ord_mul (by norm_num) (mul_ne_zero hupow hcv),
          show w.ord (-1 : F) = 0 from by
            rw [show (-1 : F) = algebraMap K F (-1) from by rw [map_neg, map_one]]
            exact ord_algebraMap_eq_zero w (by norm_num), zero_add]
      rw [hordmain, w.ord_mul hupow hcv, hordupow] at h2
      omega
  · by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero, hordmain]
    · have hord2 : w.ord (u ^ (e : ℕ) * cv) = (e : ℤ) + w.ord cv := by
        rw [w.ord_mul hupow hcv, hordupow]
      have hlt : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1))
          < w.ord (u ^ (e : ℕ) * cv) := by
        rw [hordmain, hord2]
        omega
      rw [Place.ord_add_eq_of_lt w hmne (mul_ne_zero hupow hcv) hlt, hordmain]

theorem ordDiff_D_of_pos (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ))
    (he : ((e : ℕ) : K) ≠ 0) :
    D K F s ≠ 0 ∧ w.ordDiff (D K F s) = (e : ℤ) - 1 := by
  obtain ⟨g₀, hg₀, hDeq, hord⟩ := exists_good_coeff x w hepos hords he
  have hu1 : w.ord w.uniformizer_alt = 1 := w.ord_uniformizer_alt w.exists_ord_eq_one
  have htr : Transcendental K w.uniformizer_alt :=
    w.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({w.uniformizer_alt} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x w hu1
  have hDu : D K F w.uniformizer_alt ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K _ htr
  refine ⟨?_, ?_⟩
  · rw [hDeq]; exact smul_ne_zero hg₀ hDu
  · rw [Place.ordDiff_def, diffCoeff_eq_of_eq_smul hDu hDeq, hord]

theorem ordDiff_D_of_ne_zero (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {f : F} (hf : w.ord f ≠ 0) (ht : (((w.ord f).natAbs : ℕ) : K) ≠ 0) :
    w.ordDiff (D K F f) = w.ord f - 1 := by
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hf; exact hf rfl
  rcases lt_or_gt_of_ne hf with hneg | hpos
  ·
    have hordinv : w.ord f⁻¹ = ((w.ord f).natAbs : ℤ) := by
      rw [Place.ord_inv]; omega
    have hepos : 0 < (w.ord f).natAbs := Int.natAbs_pos.mpr hf
    obtain ⟨hDinv, hordD⟩ := ordDiff_D_of_pos x w hepos hordinv ht

    have hrel : D K F f = (-(f ^ 2)) • D K F f⁻¹ := by
      have h1 : D K F (f * f⁻¹) = 0 := by rw [mul_inv_cancel₀ hf0, Derivation.map_one_eq_zero]
      rw [Derivation.leibniz] at h1

      have h2 : f⁻¹ • D K F f = -(f • D K F f⁻¹) := eq_neg_of_add_eq_zero_right h1
      have h3 : D K F f = f • (f⁻¹ • D K F f) := by rw [smul_smul, mul_inv_cancel₀ hf0, one_smul]
      rw [h3, h2, smul_neg, smul_smul, ← neg_smul, pow_two]
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
      Algebra.IsAlgebraic.of_finite _ _
    rw [hrel, Place.ordDiff_smul_of_perfectField x w (neg_ne_zero.mpr (pow_ne_zero 2 hf0)) hDinv, hordD,
      show -(f ^ 2) = (-1 : F) * f ^ 2 by ring, w.ord_mul (by norm_num) (pow_ne_zero 2 hf0),
      show w.ord (-1 : F) = 0 from by
        rw [show (-1 : F) = algebraMap K F (-1) from by rw [map_neg, map_one]]
        exact ord_algebraMap_eq_zero w (by norm_num),
      show f ^ 2 = f ^ ((2 : ℕ) : ℤ) from (zpow_natCast f 2).symm, Place.ord_zpow]
    omega
  · have hords : w.ord f = (((w.ord f).natAbs : ℕ) : ℤ) := by omega
    have hepos : 0 < (w.ord f).natAbs := Int.natAbs_pos.mpr hf
    obtain ⟨-, hordD⟩ := ordDiff_D_of_pos x w hepos hords ht
    rw [hordD]; omega

end CDivJ.TameOrder

namespace CDivJ
namespace FinDim

open AlgebraicCurve ModularCurve

theorem finiteDimensional_adjoin_jGeomGen (k : Type*) [Field k] (N : ℕ) [NeZero N]
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)] :
    FiniteDimensional ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) := by
  set F := ↥(modularFunctionFieldC k N)
  set K₀ := IntermediateField.adjoin k ({jGeomGen k N} : Set F) with hK₀
  let jN : F := ⟨jqNModC k N, jqNModC_mem k N⟩

  have hjN : jN ∈ IntermediateField.adjoin K₀ ({jN} : Set F) :=
    IntermediateField.subset_adjoin K₀ _ (Set.mem_singleton _)
  have htop : IntermediateField.adjoin K₀ ({jN} : Set F) = ⊤ := by
    rw [eq_top_iff]
    intro z _

    let E : IntermediateField k F := (IntermediateField.adjoin K₀ ({jN} : Set F)).restrictScalars k
    have hval : (modularFunctionFieldC k N) ≤ (E.map (modularFunctionFieldC k N).val) := by
      unfold modularFunctionFieldC
      rw [IntermediateField.adjoin_le_iff]
      intro s hs
      rcases hs with rfl | rfl
      · refine ⟨jGeomGen k N, ?_, rfl⟩
        show (jGeomGen k N : F) ∈ IntermediateField.adjoin K₀ ({jN} : Set F)
        have : (jGeomGen k N : F) ∈ K₀ := IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
        exact (IntermediateField.algebraMap_mem _ (⟨_, this⟩ : K₀))
      · exact ⟨jN, hjN, rfl⟩
    obtain ⟨z', hz', hzz'⟩ := hval z.2
    have : z' = z := Subtype.ext hzz'
    rw [← this]
    exact hz'
  haveI : FiniteDimensional K₀ ↥(IntermediateField.adjoin K₀ ({jN} : Set F)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic jN).isIntegral
  rw [htop] at this
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K₀) (E := F)).toLinearEquiv

end CDivJ.FinDim

namespace CDivJ
namespace Values

open AlgebraicCurve IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (ha : a ∈ maximalIdeal v.toValuationSubring) (ha0 : (a : F) ≠ 0) : 0 < v.ord (a : F) := by
  by_contra hle
  push_neg at hle
  have h0 : 0 ≤ v.ord (a : F) := v.ord_nonneg_of_mem a.2
  have heq : v.ord (a : F) = 0 := le_antisymm hle h0
  have hinv : (a : F)⁻¹ ∈ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg (inv_ne_zero ha0), v.ord_inv, heq, neg_zero]
  have hunit : IsUnit a := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(a : F)⁻¹, hinv⟩, ?_⟩
    ext
    simp [mul_inv_cancel₀ ha0]
  exact (mem_maximalIdeal _).mp ha hunit

theorem sub_algebraMap_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (c : K) :
    f - algebraMap K F c ∈ v.toValuationSubring :=
  sub_mem hf (v.algebraMap_mem' c)

theorem residue_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : K) :
    residue v.toValuationSubring ⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩
      = algebraMap K v.ResidueField (v.evalAt f) - algebraMap K v.ResidueField c := by
  have hsplit : (⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - algebraMap K v.toValuationSubring c := by
    apply Subtype.ext
    push_cast
    rw [v.coe_algebraMap]
  rw [hsplit, map_sub, v.algebraMap_evalAt hv hf]
  congr 1

theorem ord_sub_algebraMap_evalAt_pos (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : (⟨f - algebraMap K F (v.evalAt f), sub_algebraMap_mem v hf _⟩ : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
    rw [← residue_eq_zero_iff, residue_sub_algebraMap v hv hf, sub_self]
  exact ord_pos_of_mem_maximalIdeal v hmem hne

theorem ord_sub_algebraMap_eq_zero_of_ne (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) {c : K} (hc : c ≠ v.evalAt f) :
    v.ord (f - algebraMap K F c) = 0 := by
  have hnot : (⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩ : v.toValuationSubring)
      ∉ maximalIdeal v.toValuationSubring := by
    rw [← residue_eq_zero_iff, residue_sub_algebraMap v hv hf, sub_eq_zero]
    exact fun h => hc (v.algebraMap_residueField_injective h).symm
  have hunit : IsUnit (⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩ : v.toValuationSubring) := by
    by_contra h
    exact hnot ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hunit
  have := v.ord_coe_unit u
  rw [hu] at this
  exact this

theorem isCurveOver_cast {L : Type*} [Field L] [Algebra K L]
    {E E' : IntermediateField K L} (h : E = E') (hE : IsCurveOver K ↥E) : IsCurveOver K ↥E' := by
  subst h; exact hE

end CDivJ.Values

namespace CDivJ

open AlgebraicCurve ModularCurve KaehlerDifferential IsLocalRing CDivJ.TameOrder CDivJ.FinDim CDivJ.Values

theorem cast_ne_zero_of_lt (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] {n : ℕ} (h0 : n ≠ 0) (hn : n < p) :
    ((n : ℕ) : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h) (not_le.mpr hn)

theorem ordDiff_D_jGeomGen_of_isAffineGeomPlace
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N)]
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : IsAffineGeomPlace K N x) :
    x.ordDiff (D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) = (placeRamificationJ N x : ℤ) - 1 := by
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI := finiteDimensional_adjoin_jGeomGen K N
  haveI : IsCurveOver K ↥(modularFunctionFieldC K N) :=
    isCurveOver_cast (modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN).symm
      (isCurveOver_modularFunctionFieldFullC K N)
  have hrat : x.IsRational := (x.isRational_iff_deg_eq_one).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed x)
  set j : ↥(modularFunctionFieldC K N) := jGeomGen K N with hjdef
  set a : K := x.evalAt j with hadef
  have hjmem : j ∈ x.toValuationSubring := hx.1
  have hjne : ∀ c : K, j - algebraMap K _ c ≠ 0 := by
    intro c hc
    apply transcendental_jqModC K
    have hval : (jqModC K : LaurentSeries K) = algebraMap K (LaurentSeries K) c := by
      have := congrArg Subtype.val (sub_eq_zero.mp hc)
      first | exact this | simpa using this
    rw [hval]
    exact isAlgebraic_algebraMap c
  have hepos : 0 < x.ord (j - algebraMap K _ a) := ord_sub_algebraMap_evalAt_pos x hrat hjmem (hjne a)
  have he : (placeRamificationJ N x : ℤ) = x.ord (j - algebraMap K _ a) := by
    show (((x.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N)
      (x.evalAt (jGeomGen K N)))).toNat : ℕ) : ℤ) = _
    rw [Int.toNat_of_nonneg hepos.le]
  have he0 : 0 < placeRamificationJ N x := by
    have : (0 : ℤ) < (placeRamificationJ N x : ℤ) := by rw [he]; exact hepos
    exact_mod_cast this
  have hdvd : placeRamificationJ N x ∣ jWidth a := placeRamificationJ_dvd_jWidth_of_ord_pos (q := p) hp5 hpN he0
  have hle3 : placeRamificationJ N x ≤ 3 := by
    have hw : jWidth a ≤ 3 := by unfold jWidth; split_ifs <;> omega
    have hwpos : 0 < jWidth a := by unfold jWidth; split_ifs <;> omega
    exact (Nat.le_of_dvd hwpos hdvd).trans hw

  have ht : (((x.ord (j - algebraMap K _ a)).natAbs : ℕ) : K) ≠ 0 := by
    rw [← he, Int.natAbs_natCast]
    exact cast_ne_zero_of_lt p K he0.ne' (by omega)

  have hD : D K ↥(modularFunctionFieldC K N) (j - algebraMap K _ a) = D K _ j := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  rw [← hD, ordDiff_D_of_ne_zero (jGeomGen K N) x hepos.ne' ht, he]

theorem ordDiff_D_jGeomGen_of_ord_neg
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [CharP K p] [PerfectField K]
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N)]
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.ord (jGeomGen K N) < 0)
    (ht : (((x.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0) :
    x.ordDiff (D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) = x.ord (jGeomGen K N) - 1 := by
  haveI := finiteDimensional_adjoin_jGeomGen K N
  exact ordDiff_D_of_ne_zero (jGeomGen K N) x hx.ne ht

end CDivJ

namespace L2A

open AlgebraicCurve ModularCurve KaehlerDifferential CDivJ.TameOrder CDivJ.FinDim CDivJ.Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def dElt (w : Place K F) : F := ((IsDiscreteValuationRing.exists_irreducible w.toValuationSubring).choose : F)

theorem dCoord_eq (w : Place K F) : w.dCoord = D K F (dElt w) := rfl

theorem ord_dElt (w : Place K F) : w.ord (dElt w) = 1 :=
  w.ord_coe_irreducible (IsDiscreteValuationRing.exists_irreducible w.toValuationSubring).choose_spec

variable [PerfectField K]

theorem exists_good_coeff_dCoord (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ))
    (he : ((e : ℕ) : K) ≠ 0) :
    ∃ g₀ : F, g₀ ≠ 0 ∧ D K F s = g₀ • w.dCoord ∧ w.ord g₀ = (e : ℤ) - 1 := by
  classical
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hords
    omega
  set u := dElt w with hudef
  have hu1 : w.ord u = 1 := ord_dElt w
  rw [dCoord_eq]
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hu1
    exact one_ne_zero hu1.symm
  have hupow : u ^ (e : ℕ) ≠ 0 := pow_ne_zero _ hune
  have hordupow : w.ord (u ^ (e : ℕ)) = (e : ℤ) := by
    rw [show u ^ (e : ℕ) = u ^ ((e : ℕ) : ℤ) from (zpow_natCast u e).symm,
      Place.ord_zpow, hu1, mul_one]
  set c : F := s / u ^ (e : ℕ) with hcdef
  have hcne : c ≠ 0 := div_ne_zero hsne hupow
  have hordc : w.ord c = 0 := by
    rw [hcdef, div_eq_mul_inv, w.ord_mul hsne (inv_ne_zero hupow), Place.ord_inv,
      hordupow, hords]
    ring
  have hs_eq : s = c * u ^ (e : ℕ) := (div_mul_cancel₀ s hupow).symm
  have heF : ((e : ℕ) : F) ≠ 0 := by
    rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact (map_ne_zero _).mpr he
  have hordeF : w.ord ((e : ℕ) : F) = 0 := by
    rw [show ((e : ℕ) : F) = algebraMap K F ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact ord_algebraMap_eq_zero w he
  have htr : Transcendental K u := w.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({u} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x w hu1
  have hDu : D K F u ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K u htr
  set cv := Place.diffCoeff u (D K F c) with hcvdef
  have hDc : D K F c = cv • D K F u :=
    (Place.diffCoeff_smul_D
      ((KaehlerDifferential.exists_unique_smul_D_of_transcendental K u htr (D K F c)).exists)).symm
  have hcv0 : 0 ≤ w.ord cv :=
    Place.ord_diffCoeff_D_nonneg_of_isSeparable x w hu1 (le_of_eq hordc.symm)
  have hD : D K F s = (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv) • D K F u := by
    conv_lhs => rw [hs_eq]
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDc]
    rw [← Nat.cast_smul_eq_nsmul F e (u ^ ((e : ℕ) - 1) • D K F u)]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
  have hmne : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcne heF) (pow_ne_zero _ hune)
  have hordmain : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1)) = (e : ℤ) - 1 := by
    rw [w.ord_mul (mul_ne_zero hcne heF) (pow_ne_zero _ hune),
      w.ord_mul hcne heF, hordc, hordeF,
      show u ^ ((e : ℕ) - 1) = u ^ (((e : ℕ) - 1 : ℕ) : ℤ) from (zpow_natCast u _).symm,
      Place.ord_zpow, hu1, mul_one]
    have : (((e : ℕ) - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    omega
  refine ⟨c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv, ?_, hD, ?_⟩
  · by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero]
      exact hmne
    · intro h0
      have h1 : c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1) = -(u ^ (e : ℕ) * cv) := by
        linear_combination h0
      have h2 : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1))
          = w.ord (u ^ (e : ℕ) * cv) := by
        rw [h1, show -(u ^ (e : ℕ) * cv) = (-1 : F) * (u ^ (e : ℕ) * cv) by ring,
          w.ord_mul (by norm_num) (mul_ne_zero hupow hcv),
          show w.ord (-1 : F) = 0 from by
            rw [show (-1 : F) = algebraMap K F (-1) from by rw [map_neg, map_one]]
            exact ord_algebraMap_eq_zero w (by norm_num), zero_add]
      rw [hordmain, w.ord_mul hupow hcv, hordupow] at h2
      omega
  · by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero, hordmain]
    · have hord2 : w.ord (u ^ (e : ℕ) * cv) = (e : ℤ) + w.ord cv := by
        rw [w.ord_mul hupow hcv, hordupow]
      have hlt : w.ord (c * ((e : ℕ) : F) * u ^ ((e : ℕ) - 1))
          < w.ord (u ^ (e : ℕ) * cv) := by
        rw [hordmain, hord2]
        omega
      rw [Place.ord_add_eq_of_lt w hmne (mul_ne_zero hupow hcv) hlt, hordmain]

variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem ordDifferential_D_of_pos (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {s : F} {e : ℕ} (hepos : 0 < e) (hords : w.ord s = (e : ℤ))
    (he : ((e : ℕ) : K) ≠ 0) :
    w.differentialCoeff (D K F s) ≠ 0 ∧ w.ordDifferential (D K F s) = (e : ℤ) - 1 := by
  obtain ⟨g₀, hg₀, hDeq, hord⟩ := exists_good_coeff_dCoord x w hepos hords he
  have hc : w.differentialCoeff (D K F s) = g₀ := w.differentialCoeff_unique hDeq
  exact ⟨by rw [hc]; exact hg₀, by rw [Place.ordDifferential, hc, hord]⟩

theorem ordDifferential_D_of_ne_zero (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (w : Place K F) {f : F} (hf : w.ord f ≠ 0) (ht : (((w.ord f).natAbs : ℕ) : K) ≠ 0) :
    w.ordDifferential (D K F f) = w.ord f - 1 := by
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hf; exact hf rfl
  rcases lt_or_gt_of_ne hf with hneg | hpos
  · have hordinv : w.ord f⁻¹ = ((w.ord f).natAbs : ℤ) := by
      rw [Place.ord_inv]; omega
    have hepos : 0 < (w.ord f).natAbs := Int.natAbs_pos.mpr hf
    obtain ⟨hDinv, hordD⟩ := ordDifferential_D_of_pos x w hepos hordinv ht
    have hrel : D K F f = (-(f ^ 2)) • D K F f⁻¹ := by
      have h1 : D K F (f * f⁻¹) = 0 := by rw [mul_inv_cancel₀ hf0, Derivation.map_one_eq_zero]
      rw [Derivation.leibniz] at h1
      have h2 : f⁻¹ • D K F f = -(f • D K F f⁻¹) := eq_neg_of_add_eq_zero_right h1
      have h3 : D K F f = f • (f⁻¹ • D K F f) := by rw [smul_smul, mul_inv_cancel₀ hf0, one_smul]
      rw [h3, h2, smul_neg, smul_smul, ← neg_smul, pow_two]
    rw [hrel, w.ordDifferential_smul (neg_ne_zero.mpr (pow_ne_zero 2 hf0)) hDinv, hordD,
      show -(f ^ 2) = (-1 : F) * f ^ 2 by ring, w.ord_mul (by norm_num) (pow_ne_zero 2 hf0),
      show w.ord (-1 : F) = 0 from by
        rw [show (-1 : F) = algebraMap K F (-1) from by rw [map_neg, map_one]]
        exact ord_algebraMap_eq_zero w (by norm_num),
      show f ^ 2 = f ^ ((2 : ℕ) : ℤ) from (zpow_natCast f 2).symm, Place.ord_zpow]
    omega
  · have hords : w.ord f = (((w.ord f).natAbs : ℕ) : ℤ) := by omega
    have hepos : 0 < (w.ord f).natAbs := Int.natAbs_pos.mpr hf
    obtain ⟨-, hordD⟩ := ordDifferential_D_of_pos x w hepos hords ht
    rw [hordD]; omega

end L2A

namespace L2A
namespace Modular

open AlgebraicCurve ModularCurve KaehlerDifferential IsLocalRing CDivJ.TameOrder CDivJ.FinDim CDivJ.Values L2A

theorem main (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    [∀ w : Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates] [Nontrivial Ω[↥(modularFunctionFieldC K N)⁄K]]
    (w : Place K ↥(modularFunctionFieldC K N)) :
    (IsAffineGeomPlace K N w →
        w.ordDifferential (D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) = (placeRamificationJ N w : ℤ) - 1) ∧
    (w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0 →
        w.ordDifferential (D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) = w.ord (jGeomGen K N) - 1) := by
  haveI : PerfectField K := IsAlgClosed.perfectField K

  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N) :=
    (finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data
      (isSeparable_jqNModC_of_natCast_ne_zero K N hN)).1
  refine ⟨fun hx => ?_, fun hneg ht => ordDifferential_D_of_ne_zero (jGeomGen K N) w hneg.ne ht⟩

  haveI : IsCurveOver K ↥(modularFunctionFieldC K N) :=
    isCurveOver_cast (modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN).symm
      (isCurveOver_modularFunctionFieldFullC K N)
  have hrat : w.IsRational := (w.isRational_iff_deg_eq_one).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)
  set j : ↥(modularFunctionFieldC K N) := jGeomGen K N with hjdef
  set a : K := w.evalAt j with hadef
  have hjmem : j ∈ w.toValuationSubring := hx.1
  have hjne : ∀ c : K, j - algebraMap K _ c ≠ 0 := by
    intro c hc
    apply transcendental_jqModC K
    have hval : (jqModC K : LaurentSeries K) = algebraMap K (LaurentSeries K) c := by
      have := congrArg Subtype.val (sub_eq_zero.mp hc)
      first | exact this | simpa using this
    rw [hval]
    exact isAlgebraic_algebraMap c
  have hepos : 0 < w.ord (j - algebraMap K _ a) := ord_sub_algebraMap_evalAt_pos w hrat hjmem (hjne a)
  have he : (placeRamificationJ N w : ℤ) = w.ord (j - algebraMap K _ a) := by
    show (((w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N)
      (w.evalAt (jGeomGen K N)))).toNat : ℕ) : ℤ) = _
    rw [Int.toNat_of_nonneg hepos.le]
  have he0 : 0 < placeRamificationJ N w := by
    have : (0 : ℤ) < (placeRamificationJ N w : ℤ) := by rw [he]; exact hepos
    exact_mod_cast this
  have hdvd : placeRamificationJ N w ∣ jWidth a := placeRamificationJ_dvd_jWidth_of_ord_pos (q := p) hp5 hpN he0
  have hle3 : placeRamificationJ N w ≤ 3 := by
    have hw : jWidth a ≤ 3 := by unfold jWidth; split_ifs <;> omega
    have hwpos : 0 < jWidth a := by unfold jWidth; split_ifs <;> omega
    exact (Nat.le_of_dvd hwpos hdvd).trans hw
  have ht : (((w.ord (j - algebraMap K _ a)).natAbs : ℕ) : K) ≠ 0 := by
    rw [← he, Int.natAbs_natCast]
    exact CDivJ.cast_ne_zero_of_lt p K he0.ne' (by omega)
  have hD : D K ↥(modularFunctionFieldC K N) (j - algebraMap K _ a) = D K _ j := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  rw [← hD, ordDifferential_D_of_ne_zero (jGeomGen K N) w hepos.ne' ht, he]

end L2A.Modular

open AlgebraicCurve ModularCurve in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) :
    (IsAffineGeomPlace K N w →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))
        = (placeRamificationJ N w : ℤ) - 1) ∧
    (w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0 →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))
        = w.ord (jGeomGen K N) - 1) :=
  L2A.Modular.main p hp5 N hpN K w

end S_ModularCurve_ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
end P2MW
export P2MW.S_ModularCurve_ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero (solution)
