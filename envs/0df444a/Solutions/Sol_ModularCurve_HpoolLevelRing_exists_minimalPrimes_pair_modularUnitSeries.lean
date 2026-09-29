-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_minimalPrimes_pair_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2ff9c956-c2a7-5efe-8209-d2c5ac893ce8

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_minimalPrimes_pair_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

open ModularCurve AlgebraicCurve Polynomial

namespace DICTALG

theorem mem_valuationSubring_of_isIntegral_adjoin {F : Type*} [Field F] (W : ValuationSubring F) (j x : F)
    (hj : j ∈ W) (hx : IsIntegral (Algebra.adjoin ℤ ({j} : Set F)) x) : x ∈ W := by
  have hsub : ∀ y ∈ Algebra.adjoin ℤ ({j} : Set F), y ∈ W := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.mp hz]; exact hj
    | algebraMap r => exact intCast_mem W.toSubring r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  let φ : Algebra.adjoin ℤ ({j} : Set F) →+* W :=
    { toFun := fun y => ⟨y.1, hsub y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hxW : IsIntegral W x := by
    have := hx.map_of_comp_eq φ (RingHom.id F) (RingHom.ext fun y => rfl)
    simpa using this
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := F)).mp hxW
  rw [← hy]
  exact y.2

theorem not_mem_nonunits_of_inv_mem {F : Type*} [Field F] (W : ValuationSubring F) {x : F}
    (hx0 : x ≠ 0) (hxi : x⁻¹ ∈ W) : x ∉ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt]
  have h1 : W.valuation x⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr hxi
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero W.valuation).mpr hx0))).mp h1

theorem mem_nonunits_of_inv_not_mem {F : Type*} [Field F] (W : ValuationSubring F) {x : F}
    (hx : x ∈ W) (hxi : x⁻¹ ∉ W) : x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  rw [← W.valuation_le_one_iff, not_le, map_inv₀] at hxi
  have hx0 : W.valuation x ≠ 0 := by
    intro h; rw [h, inv_zero] at hxi; exact not_lt_of_ge zero_le_one hxi
  exact (one_lt_inv₀ (zero_lt_iff.mpr hx0)).mp hxi

theorem inv_not_mem_of_mem_nonunits {F : Type*} [Field F] (W : ValuationSubring F) {x : F}
    (hx : x ∈ W.nonunits) (hx0 : x ≠ 0) : x⁻¹ ∉ W := fun h =>
  not_mem_nonunits_of_inv_mem W hx0 h hx

variable (p : ℕ) [Fact p.Prime] [NeZero p]

theorem main (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    ∃ (u v : HpoolLevelRing.Afin p) (P₀ P₁ : Ideal (HpoolLevelRing.Afin p)),
      (u : ↥(modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∧
      (v : ↥(modularFunctionFieldFull p)) = (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹ ∧
      P₀.IsPrime ∧ P₁.IsPrime ∧ P₀ ≠ P₁ ∧
      (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {P₀, P₁} ∧
      u ∉ P₀ ∧ u ∈ P₁ ∧ v ∈ P₀ ∧ v ∉ P₁ := by
  classical
  have hpp : p.Prime := Fact.out

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hne, hgen, hcomplete, ht, -, -⟩ :=
    DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  have hM := DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
  obtain ⟨hgauss, σ, hσj, hσjp, hσσ, hσW⟩ :=
    DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
  obtain ⟨huA, hvA⟩ := modularUnitSeries_mem_chartAlgFin_int p hmem
  set uF : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, hmem⟩ with huF
  have hu0 : uF ≠ 0 := fun h => modularUnitSeries_ne_zero p (congrArg Subtype.val h)
  have hp0 : (p : ↥(modularFunctionFieldFull p)) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero

  have hX : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  have hjW₀ : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ W₀ := by simpa using (hgen 0 Polynomial.X hX).1
  have hjW₁ : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ W₁ := by simpa using (hgen 1 Polynomial.X hX).1
  have hAW₀ : ∀ a : HpoolLevelRing.Afin p, (a : ↥(modularFunctionFieldFull p)) ∈ W₀ :=
    fun a => mem_valuationSubring_of_isIntegral_adjoin W₀ _ _ hjW₀ a.2
  have hAW₁ : ∀ a : HpoolLevelRing.Afin p, (a : ↥(modularFunctionFieldFull p)) ∈ W₁ :=
    fun a => mem_valuationSubring_of_isIntegral_adjoin W₁ _ _ hjW₁ a.2

  let φ₀ : HpoolLevelRing.Afin p →+* W₀ :=
    { toFun := fun a => ⟨a, hAW₀ a⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φ₁ : HpoolLevelRing.Afin p →+* W₁ :=
    { toFun := fun a => ⟨a, hAW₁ a⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let P₀ : Ideal (HpoolLevelRing.Afin p) := (IsLocalRing.maximalIdeal W₀).comap φ₀
  let P₁ : Ideal (HpoolLevelRing.Afin p) := (IsLocalRing.maximalIdeal W₁).comap φ₁
  have hP₀ : ∀ a : HpoolLevelRing.Afin p, a ∈ P₀ ↔ (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits := fun a => by
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
  have hP₁ : ∀ a : HpoolLevelRing.Afin p, a ∈ P₁ ↔ (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits := fun a => by
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
  haveI : P₀.IsPrime := Ideal.comap_isPrime φ₀ _
  haveI : P₁.IsPrime := Ideal.comap_isPrime φ₁ _

  have hp1 : ¬ p ∣ 1 := fun h => hpp.one_lt.ne' (Nat.dvd_one.mp h)
  obtain ⟨W', h1, h2, -⟩ := exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd 1 p hp1
  have hmem₁ : modularUnitSeries p ∈ modularFunctionFieldFull (1 * p) :=
    full_degeneracy_le (N := p) (M := 1 * p) ⟨1, by ring⟩ hmem
  obtain ⟨⟨x, hx0, hxu⟩, -, -, -⟩ :=
    modularUnitSeries_mem_valuationSubring_pair_of_not_dvd 1 p hp1 hmem₁ (W' 0) (W' 1) h1 h2

  have huW₀ : uF ∈ W₀ := (hgauss uF).mpr ⟨x, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one, ← hxu]⟩
  have huiW₀ : uF⁻¹ ∈ W₀ := (hgauss uF⁻¹).mpr ⟨1, x, hx0, by
    rw [map_one, ← hxu]; exact inv_mul_cancel₀ (modularUnitSeries_ne_zero p)⟩
  have hpW₀ : (p : ↥(modularFunctionFieldFull p)) ∈ W₀ := natCast_mem W₀ p
  have hpiW₀ : (p : ↥(modularFunctionFieldFull p))⁻¹ ∉ W₀ := inv_not_mem_of_mem_nonunits W₀ hp₀ hp0

  have hwex := exists_isFrickeAutFull_of_neZero p
  set w := frickeInvolutionFull p with hwdef
  have hw : IsFrickeAutFull p w := isFrickeAutFull_frickeInvolutionFull p hwex
  have hjF1 : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) = ⟨qExpand ℚ 1 jq, jqd_mem_full p (Dvd.intro p (one_mul p))⟩ :=
    Subtype.ext (show (IgusaScheme.jFull p : LaurentSeries ℚ) = qExpand ℚ 1 jq by rw [qExpand_one_apply]; rfl)
  have hjpF : (jp : ↥(modularFunctionFieldFull p)) = ⟨qExpand ℚ p jq, jqd_mem_full p (Dvd.intro_left 1 (one_mul p))⟩ := Subtype.ext hjp
  have hσw : ∀ z : ↥(modularFunctionFieldFull p), σ z = w z := by

    have hgen_eq : ∀ (x : LaurentSeries ℚ) (hx : x ∈ divisorExpansions p),
        σ ⟨x, IntermediateField.subset_adjoin ℚ _ hx⟩ = w ⟨x, IntermediateField.subset_adjoin ℚ _ hx⟩ := by
      intro x hx
      obtain ⟨d, hd, hdp, rfl⟩ := hx
      rcases (Nat.dvd_prime hpp).mp hdp with h1 | h1
      ·
        have e1 : (⟨qExpand ℚ d jq, IntermediateField.subset_adjoin ℚ _ ⟨d, hd, hdp, rfl⟩⟩ : ↥(modularFunctionFieldFull p)) =
            IgusaScheme.jFull p :=
          Subtype.ext (show qExpand ℚ d jq = (IgusaScheme.jFull p : LaurentSeries ℚ) by
            rw [qExpand_congr h1, qExpand_one_apply]; rfl)
        have e2 := hw 1 p (one_mul p) inferInstance inferInstance
        rw [← hjF1, ← hjpF] at e2
        rw [e1, hσj, e2]
      ·
        have e1 : (⟨qExpand ℚ d jq, IntermediateField.subset_adjoin ℚ _ ⟨d, hd, hdp, rfl⟩⟩ : ↥(modularFunctionFieldFull p)) = (jp : ↥(modularFunctionFieldFull p)) :=
          Subtype.ext (show qExpand ℚ d jq = ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) by rw [qExpand_congr h1]; exact hjp.symm)
        have e2 := hw p 1 (mul_one p) inferInstance inferInstance
        rw [← hjF1, ← hjpF] at e2
        rw [e1, hσjp, e2]
    intro z
    obtain ⟨x, hx⟩ := z
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hgen_eq x hx
    | algebraMap r =>
      have : (⟨algebraMap ℚ (LaurentSeries ℚ) r, IntermediateField.algebraMap_mem _ r⟩ : ↥(modularFunctionFieldFull p)) = algebraMap ℚ ↥(modularFunctionFieldFull p) r :=
        Subtype.ext (by simp)
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, add_mem hx hy⟩ : ↥(modularFunctionFieldFull p)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
    | inv x hx ihx =>
      have : (⟨x⁻¹, inv_mem hx⟩ : ↥(modularFunctionFieldFull p)) = (⟨x, hx⟩ : ↥(modularFunctionFieldFull p))⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihx]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, mul_mem hx hy⟩ : ↥(modularFunctionFieldFull p)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

  set vF : ↥(modularFunctionFieldFull p) := (p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹ with hvF
  have hinj : Function.Injective (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) := (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).injective
  have hcoe : ∀ z : ↥(modularFunctionFieldFull p), algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ) z = (z : LaurentSeries ℚ) := fun z => rfl
  have hσu : σ uF = vF := by
    rw [hσw]
    apply hinj
    have h1 := coe_frickeInvolutionFull_modularUnitSeries_of_neZero p hmem
    rw [← hwdef] at h1
    rw [hcoe, h1, hvF, map_mul, map_pow, map_inv₀, map_natCast, hcoe uF]
    have hC : (HahnSeries.C ((p : ℚ) ^ 12) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 := by
      rw [map_pow, map_natCast]
    first
      | rw [Algebra.smul_def, ← HahnSeries.C_eq_algebraMap, hC]
      | rw [← HahnSeries.C_mul_eq_smul, hC]
  have hv0 : vF ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) (inv_ne_zero hu0)

  have hvW₀ : vF ∈ W₀ := mul_mem (pow_mem hpW₀ 12) huiW₀
  have hviW₀ : vF⁻¹ ∉ W₀ := by
    intro h
    apply hpiW₀
    have key : (p : ↥(modularFunctionFieldFull p))⁻¹ = vF⁻¹ * uF⁻¹ * (p : ↥(modularFunctionFieldFull p)) ^ 11 := by
      rw [hvF]; field_simp
    rw [key]
    exact mul_mem (mul_mem h huiW₀) (pow_mem hpW₀ 11)
  have huW₁ : uF ∈ W₁ := (hσW uF).mpr (by rw [hσu]; exact hvW₀)
  have huiW₁ : uF⁻¹ ∉ W₁ := fun h => hviW₀ (by
    have := (hσW uF⁻¹).mp h
    rwa [map_inv₀, hσu] at this)
  have hσv : σ vF = uF := by
    rw [hvF, map_mul, map_pow, map_natCast, map_inv₀, hσu, hvF]
    field_simp
  have hvW₁ : vF ∈ W₁ := (hσW vF).mpr (by rw [hσv]; exact huW₀)
  have hviW₁ : vF⁻¹ ∈ W₁ := (hσW vF⁻¹).mpr (by rw [map_inv₀, hσv]; exact huiW₀)

  let uA : HpoolLevelRing.Afin p := ⟨uF, huA⟩
  let vA : HpoolLevelRing.Afin p := ⟨vF, hvA⟩
  have huP₀ : uA ∉ P₀ := fun h => not_mem_nonunits_of_inv_mem W₀ hu0 huiW₀ ((hP₀ uA).mp h)
  have huP₁ : uA ∈ P₁ := (hP₁ uA).mpr (mem_nonunits_of_inv_not_mem W₁ huW₁ huiW₁)
  have hvP₀ : vA ∈ P₀ := (hP₀ vA).mpr (mem_nonunits_of_inv_not_mem W₀ hvW₀ hviW₀)
  have hvP₁ : vA ∉ P₁ := fun h => not_mem_nonunits_of_inv_mem W₁ hv0 hviW₁ ((hP₁ vA).mp h)
  have hneP : P₀ ≠ P₁ := fun h => huP₀ (h ▸ huP₁)

  have hmin : (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {P₀, P₁} := by
    ext 𝔭
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hM𝔭 := hM 𝔭
    rw [hM𝔭]
    constructor
    · rintro (h | h)
      · left; exact Ideal.ext fun a => (h a).trans (hP₀ a).symm
      · right; exact Ideal.ext fun a => (h a).trans (hP₁ a).symm
    · rintro (rfl | rfl)
      · left; exact fun a => hP₀ a
      · right; exact fun a => hP₁ a
  exact ⟨uA, vA, P₀, P₁, rfl, rfl, inferInstance, inferInstance, hneP, hmin, huP₀, huP₁, hvP₀, hvP₁⟩

end DICTALG

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    ∃ (u v : HpoolLevelRing.Afin p) (P₀ P₁ : Ideal (HpoolLevelRing.Afin p)),
      (u : ↥(ModularCurve.modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∧
      (v : ↥(ModularCurve.modularFunctionFieldFull p)) = (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p))⁻¹ ∧
      P₀.IsPrime ∧ P₁.IsPrime ∧ P₀ ≠ P₁ ∧
      (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {P₀, P₁} ∧
      u ∉ P₀ ∧ u ∈ P₁ ∧ v ∈ P₀ ∧ v ∉ P₁ :=
  DICTALG.main p hmem

end S_ModularCurve_HpoolLevelRing_exists_minimalPrimes_pair_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_minimalPrimes_pair_modularUnitSeries (solution)
