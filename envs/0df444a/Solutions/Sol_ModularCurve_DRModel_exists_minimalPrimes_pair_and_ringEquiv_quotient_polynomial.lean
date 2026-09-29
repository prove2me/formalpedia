-- Prove2me | solution 1 for ModularCurve.DRModel.exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bd1aa21d-034d-5b95-bf9c-fa48293c2b03

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
import Theorems.Thm_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X
import Theorems.Thm_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial.ModularCurve AlgebraicCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme qExpand jq modularFunctionFieldFull DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair DRModel.exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair"
namespace DRModel
p2m_export "ModularCurve.DRModel" "mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair"
namespace C1jAux
p2m_open "ModularCurve.DRModel ModularCurve"

theorem mem_of_isIntegral_adjoin {K : Type*} [Field K] (W : ValuationSubring K) (s : Set K)
    (hs : s ⊆ W) (x : K) (hx : IsIntegral ↥(Algebra.adjoin ℤ s) x) : x ∈ W := by
  have hle : ∀ y ∈ Algebra.adjoin ℤ s, y ∈ W := by
    intro y hy
    have : Algebra.adjoin ℤ s ≤ subalgebraOfSubring W.toSubring := Algebra.adjoin_le hs
    exact this hy
  let φ : ↥(Algebra.adjoin ℤ s) →+* ↥W :=
    (Algebra.adjoin ℤ s).val.toRingHom.codRestrict W.toSubring fun y => hle y y.2
  have hx' : IsIntegral ↥W x :=
    hx.map_of_comp_eq φ (RingHom.id K) (by ext; rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W) (K := K)).mp hx'
  rw [← hy]
  exact y.2

end ModularCurve.DRModel.C1jAux

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits) :
    let A := TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    let j : ↥A := TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    ∃ 𝔭₀ 𝔭₁ : Ideal ↥A,
      (∀ a : ↥A, a ∈ 𝔭₀ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)) ∧
      (∀ a : ↥A, a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)) ∧
      (Ideal.span {((p : ℕ) : ↥A)}).minimalPrimes = {𝔭₀, 𝔭₁} ∧ 𝔭₀ ≠ 𝔭₁ ∧
      (∃ e₀ : (↥A ⧸ 𝔭₀) ≃+* Polynomial (ZMod p),
          e₀ (Ideal.Quotient.mk 𝔭₀ j) = X ∧ e₀ (Ideal.Quotient.mk 𝔭₀ jp) = X ^ p) ∧
      (∃ e₁ : (↥A ⧸ 𝔭₁) ≃+* Polynomial (ZMod p),
          e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X ∧ e₁ (Ideal.Quotient.mk 𝔭₁ j) = X ^ p) := by
  intro A j
  classical

  have hXmap : (X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by rw [Polynomial.map_X]; exact X_ne_zero
  have hjW : ∀ i : Fin 2, (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i) := by
    intro i
    have := (hgen i X hXmap).1
    simpa only [eval₂_X] using this
  have hAW : ∀ i : Fin 2, ∀ a : ↥A, (a : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i) := by
    intro i a
    refine ModularCurve.DRModel.C1jAux.mem_of_isIntegral_adjoin _ {IgusaScheme.jFull p}
      (Set.singleton_subset_iff.mpr (hjW i)) _ ?_
    exact (TwoChartIntegralModel.mem_chartAlg_iff ℤ ↥(modularFunctionFieldFull p)).mp a.2
  have hAW₀ : ∀ a : ↥A, (a : ↥(modularFunctionFieldFull p)) ∈ W₀ := fun a => by simpa using hAW 0 a
  have hAW₁ : ∀ a : ↥A, (a : ↥(modularFunctionFieldFull p)) ∈ W₁ := fun a => by simpa using hAW 1 a

  let toW₀ : ↥A →+* ↥W₀ := A.val.toRingHom.codRestrict W₀.toSubring hAW₀
  let toW₁ : ↥A →+* ↥W₁ := A.val.toRingHom.codRestrict W₁.toSubring hAW₁
  let 𝔭₀ : Ideal ↥A := (IsLocalRing.maximalIdeal ↥W₀).comap toW₀
  let 𝔭₁ : Ideal ↥A := (IsLocalRing.maximalIdeal ↥W₁).comap toW₁
  have h𝔭₀ : ∀ a : ↥A, a ∈ 𝔭₀ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits) := by
    intro a
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have h𝔭₁ : ∀ a : ↥A, a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits) := by
    intro a
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl

  have hM := ModularCurve.DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair p jp hjp W₀ W₁
    hp₀ hp₁ hne hgen hcomplete ht
  have hmin : (Ideal.span {((p : ℕ) : ↥A)}).minimalPrimes = {𝔭₀, 𝔭₁} := by
    ext 𝔮
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    refine (hM 𝔮).trans ?_
    constructor
    · rintro (h | h)
      · left; ext a; rw [h a, h𝔭₀ a]
      · right; ext a; rw [h a, h𝔭₁ a]
    · rintro (rfl | rfl)
      · exact Or.inl h𝔭₀
      · exact Or.inr h𝔭₁

  have hS1 := ModularCurve.DRModel.exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair p jp hjp
    W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁
  obtain ⟨e₀, he₀j, he₀jp⟩ := hS1.1 𝔭₀ h𝔭₀
  obtain ⟨e₁, he₁jp, he₁j⟩ := hS1.2 𝔭₁ h𝔭₁

  have hne𝔭 : 𝔭₀ ≠ 𝔭₁ := by
    intro heq
    refine RingEquiv.false_of_apply_eq_X_pow_of_apply_eq_X p (Nat.Prime.two_le Fact.out) (ZMod p) (↥A ⧸ 𝔭₀)
      e₀ ((Ideal.quotEquivOfEq heq).trans e₁) (Ideal.Quotient.mk 𝔭₀ j) (Ideal.Quotient.mk 𝔭₀ jp)
      he₀j he₀jp ?_ ?_
    · rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, he₁jp]
    · rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, he₁j]
  exact ⟨𝔭₀, 𝔭₁, h𝔭₀, h𝔭₁, hmin, hne𝔭, ⟨e₀, he₀j, he₀jp⟩, ⟨e₁, he₁jp, he₁j⟩⟩

end S_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial
end P2MW
export P2MW.S_ModularCurve_DRModel_exists_minimalPrimes_pair_and_ringEquiv_quotient_polynomial (solution)
