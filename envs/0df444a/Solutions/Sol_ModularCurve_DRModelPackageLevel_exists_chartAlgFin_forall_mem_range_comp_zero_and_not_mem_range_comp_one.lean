-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/33f5a899-66b4-5a3f-b8b5-7f36e67aff41

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

open ModularCurve.DRModelPackageLevel in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∃ v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q) ∨
        (((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹)) ∧
      ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
        (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
        (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
        v ∉ 𝔮.asIdeal →
        y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) :=
    hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)

  obtain ⟨huA, hvA⟩ := modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmem
  set uF : ↥(modularFunctionFieldFull (N₀ * q)) := ⟨modularUnitSeries q, hmem⟩ with huF
  let uA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨uF, huA⟩
  let vA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨(q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹, hvA⟩

  obtain ⟨W, hW₀, hW₁, hne, habove, hcomplete⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
  obtain ⟨P, hPmem, hPprime, hPne, hmin⟩ :=
    exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair N₀ q hqN W hW₀ hW₁ hne habove hcomplete
  obtain ⟨-, -, ⟨huW0, huinvW0⟩, ⟨hu'W1, hu'invW1⟩⟩ :=
    ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd N₀ q hqN hmem (W 0) (W 1) hW₀ hW₁
  have hq1 : ∀ i, (W i).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) < 1 := fun i =>
    (ValuationSubring.mem_nonunits_iff _).mp (habove i).1
  have huF0 : uF ≠ 0 := by
    intro h
    have := congrArg (fun x : ↥(modularFunctionFieldFull (N₀ * q)) => (x : LaurentSeries ℚ)) h
    simp only [huF] at this
    exact (ModularCurve.modularUnitSeries_ne_zero q) (by simpa using this)

  have hu0 : uA ∉ P 0 := by
    intro h
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 0 uA).mp h)
    have hle : (W 0).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr huinvW0
    rw [map_inv₀, inv_le_one₀ (by
      rw [Valuation.pos_iff]; exact huF0)] at hle
    exact not_lt.mpr hle hlt

  have hu1 : uA ∈ P 1 := by
    refine (hPmem 1 uA).mpr ((ValuationSubring.mem_nonunits_iff _).mpr ?_)
    have hq0 : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have hfac : (uF : ↥(modularFunctionFieldFull (N₀ * q))) = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := by
      rw [inv_mul_cancel_right₀ (pow_ne_zero _ hq0)]
    show (W 1).valuation (uA : ↥(modularFunctionFieldFull (N₀ * q))) < 1
    change (W 1).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q))) < 1
    rw [hfac, map_mul, map_pow]
    have h1 : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) ≤ 1 := ((W 1).valuation_le_one_iff _).mpr hu'W1
    calc (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) * (W 1).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12
        ≤ 1 * (W 1).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := mul_le_mul_left h1 _
      _ = (W 1).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := one_mul _
      _ < 1 := pow_lt_one₀ zero_le' (hq1 1) (by norm_num)

  have hv0 : vA ∈ P 0 := by
    refine (hPmem 0 vA).mpr ((ValuationSubring.mem_nonunits_iff _).mpr ?_)
    show (W 0).valuation ((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹) < 1
    rw [map_mul, map_pow]
    have h1 : (W 0).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr huinvW0
    have hqq : (q : ↥(modularFunctionFieldFull (N₀ * q))) = ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) := rfl
    calc (W 0).valuation (q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * (W 0).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹
        ≤ (W 0).valuation (q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * 1 := mul_le_mul_right h1 _
      _ = (W 0).valuation (q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := mul_one _
      _ < 1 := by rw [hqq]; exact pow_lt_one₀ zero_le' (hq1 0) (by norm_num)
  have hv1 : vA ∉ P 1 := by
    intro h
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 1 vA).mp h)

    have hq0 : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have hv : ((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹) = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv]; exact mul_comm _ _
    have hle : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) ≤ 1 := ((W 1).valuation_le_one_iff _).mpr hu'W1
    have hlt' : (W 1).valuation ((uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹) < 1 := by
      have : (vA : ↥(modularFunctionFieldFull (N₀ * q))) = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹ := hv
      rw [← this]; exact hlt
    rw [map_inv₀, inv_lt_one₀ (by
      rw [Valuation.pos_iff]; exact mul_ne_zero huF0 (inv_ne_zero (pow_ne_zero _ hq0)))] at hlt'
    exact not_lt.mpr hle hlt'

  obtain ⟨i, hi⟩ := exists_index_forall_mem_range_comp_zero_of_not_le N₀ q hqN 𝔓 P hPprime hmin hPne
  fin_cases i
  · refine ⟨uA, Or.inl rfl, fun κ _ _ _ _ toκ y 𝔮 hy hu𝔮 => hi κ toκ y 𝔮 hy fun j hj hle => ?_⟩
    fin_cases j
    · exact (hj rfl).elim
    · exact hu𝔮 (hle hu1)
  · refine ⟨vA, Or.inr ?_, fun κ _ _ _ _ toκ y 𝔮 hy hv𝔮 => hi κ toκ y 𝔮 hy fun j hj hle => ?_⟩
    · show (((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹ : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = _
      push_cast
      rfl
    · fin_cases j
      · exact hv𝔮 (hle hv0)
      · exact (hj rfl).elim

end S_ModularCurve_DRModelPackageLevel_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one (solution)
