-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.pt_eq_pt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/95f3a483-6bb4-54f6-8cc1-33e2cef8666a

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange
import Theorems.Thm_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary modularFunctionFieldFull laurentBaseChange realize_eq_div qExpansion_div_mem_laurentBaseChange"
namespace ComplexPlaceDictionaryOrbit
p2m_open "ModularCurve"

variable {N : ℕ}

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

scoped instance nhdsNE_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  have h : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ)).NeBot := by
    rw [map_coe_nhdsNE]; infer_instance
  exact Filter.NeBot.of_map h

theorem continuous_coe {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    Continuous (f : ℍ → ℂ) :=
  (ModularFormClass.holo f).continuous

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem ne_zero_of_apply_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    {τ : ℍ} (h : (f : ℍ → ℂ) τ ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem exists_normalised_pair {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    {τ τ' : ℍ} (hdet : (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ) :
    ∃ g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      (h₁ : ℍ → ℂ) τ ≠ 0 ∧ (h₁ : ℍ → ℂ) τ' = 0 ∧ (g₁ : ℍ → ℂ) τ' ≠ 0 := by
  set h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k :=
    ((h : ℍ → ℂ) τ') • g - ((g : ℍ → ℂ) τ') • h with hh₁
  have hval : ∀ z : ℍ, (h₁ : ℍ → ℂ) z =
      (h : ℍ → ℂ) τ' * (g : ℍ → ℂ) z - (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) z := by
    intro z
    simp [hh₁, smul_eq_mul]
  have h₁τ : (h₁ : ℍ → ℂ) τ ≠ 0 := by
    rw [hval]
    intro h0
    apply hdet
    have := sub_eq_zero.mp h0

    calc (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' = (h : ℍ → ℂ) τ' * (g : ℍ → ℂ) τ := by ring
      _ = (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := this
  have h₁τ' : (h₁ : ℍ → ℂ) τ' = 0 := by
    rw [hval]; ring
  by_cases hg : (g : ℍ → ℂ) τ' = 0
  · refine ⟨h, h₁, h₁τ, h₁τ', ?_⟩
    intro hh0
    apply hdet
    rw [hg, hh0, mul_zero, zero_mul]
  · exact ⟨g, h₁, h₁τ, h₁τ', hg⟩

section Local

variable {k : ℤ} (g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k)

def quot : LaurentSeries ℂ := qL g₁ / qL h₁

theorem quot_mul_eq (hh₁ : h₁ ≠ 0) : quot g₁ h₁ * qL h₁ = qL g₁ :=
  div_mul_cancel₀ _ (qL_ne_zero h₁ hh₁)

theorem realize_quot_eq (hh₁ : h₁ ≠ 0) {z : ℍ} (hz : (h₁ : ℍ → ℂ) z ≠ 0) :
    realize N (quot g₁ h₁) z = (g₁ : ℍ → ℂ) z / (h₁ : ℍ → ℂ) z :=
  ModularCurve.realize_eq_div N g₁ h₁ (quot g₁ h₁) (quot_mul_eq g₁ h₁ hh₁) z hz

theorem isBoundedUnder_realize_quot {τ : ℍ} (hτ : (h₁ : ℍ → ℂ) τ ≠ 0) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (quot g₁ h₁) z‖) := by
  have hh₁ : h₁ ≠ 0 := ne_zero_of_apply_ne_zero h₁ hτ
  have hcont : ContinuousAt (fun z : ℍ => (g₁ : ℍ → ℂ) z / (h₁ : ℍ → ℂ) z) τ :=
    ((continuous_coe g₁).continuousAt).div ((continuous_coe h₁).continuousAt) hτ
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(g₁ : ℍ → ℂ) z / (h₁ : ℍ → ℂ) z‖) :=
    (hcont.norm.tendsto).isBoundedUnder_le
  obtain ⟨b, hb⟩ := hbd
  rw [Filter.eventually_map] at hb
  have hne : ∀ᶠ z in 𝓝 τ, (h₁ : ℍ → ℂ) z ≠ 0 :=
    ((continuous_coe h₁).continuousAt).eventually_ne hτ
  refine ⟨b, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [nhdsWithin_le_nhds hb, nhdsWithin_le_nhds hne] with z hz hz'
  rwa [realize_quot_eq g₁ h₁ hh₁ hz']

theorem not_isBoundedUnder_realize_quot {τ' : ℍ} (hh₁ : h₁ ≠ 0)
    (hτ' : (h₁ : ℍ → ℂ) τ' = 0) (hg : (g₁ : ℍ → ℂ) τ' ≠ 0) :
    ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] τ') (fun z : ℍ => ‖realize N (quot g₁ h₁) z‖) := by
  have hne : ∀ᶠ z in 𝓝[≠] τ', (h₁ : ℍ → ℂ) z ≠ 0 := eventually_ne_zero h₁ hh₁ τ'

  have hh0 : Tendsto (fun z : ℍ => ‖(h₁ : ℍ → ℂ) z‖) (𝓝[≠] τ') (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (((continuous_coe h₁).continuousAt (x := τ')).norm).tendsto
      rw [hτ', norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [hne] with z hz
      exact norm_pos_iff.mpr hz
  have hinv : Tendsto (fun z : ℍ => ‖(h₁ : ℍ → ℂ) z‖⁻¹) (𝓝[≠] τ') atTop :=
    tendsto_inv_nhdsGT_zero.comp hh0
  have hgt : Tendsto (fun z : ℍ => ‖(g₁ : ℍ → ℂ) z‖) (𝓝[≠] τ') (𝓝 ‖(g₁ : ℍ → ℂ) τ'‖) :=
    (((continuous_coe g₁).continuousAt (x := τ')).norm).tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun z : ℍ => ‖(g₁ : ℍ → ℂ) z‖ * ‖(h₁ : ℍ → ℂ) z‖⁻¹) (𝓝[≠] τ')
      atTop :=
    Filter.Tendsto.pos_mul_atTop (norm_pos_iff.mpr hg) hgt hinv
  have hquot : Tendsto (fun z : ℍ => ‖realize N (quot g₁ h₁) z‖) (𝓝[≠] τ') atTop := by
    refine hprod.congr' ?_
    filter_upwards [hne] with z hz
    rw [realize_quot_eq g₁ h₁ hh₁ hz, norm_div, div_eq_mul_inv]
  exact not_isBoundedUnder_of_tendsto_atTop hquot

end Local

theorem pt_ne_pt_of_forall_smul_ne [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N)
    (τ τ' : ℍ) (hτ : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ') :
    D.pt τ ≠ D.pt τ' := by
  intro hpt
  obtain ⟨k, g, h, hdet⟩ :=
    ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne N τ τ' hτ
  obtain ⟨g₁, h₁, h₁τ, h₁τ', g₁τ'⟩ := exists_normalised_pair g h hdet
  have hh₁ : h₁ ≠ 0 := ne_zero_of_apply_ne_zero h₁ h₁τ

  have hmem : quot g₁ h₁ ∈ laurentBaseChange ℂ (modularFunctionFieldFull N) :=
    ModularCurve.qExpansion_div_mem_laurentBaseChange N g₁ h₁ hh₁
  set x : laurentBaseChange ℂ (modularFunctionFieldFull N) := ⟨quot g₁ h₁, hmem⟩ with hx
  have hxcoe : (x : LaurentSeries ℂ) = quot g₁ h₁ := rfl

  have hreg : x ∈ (D.pt τ).toValuationSubring := by
    rw [D.mem_pt_iff τ x, hxcoe]
    exact isBoundedUnder_realize_quot g₁ h₁ h₁τ

  rw [hpt, D.mem_pt_iff τ' x, hxcoe] at hreg
  exact not_isBoundedUnder_realize_quot g₁ h₁ hh₁ h₁τ' g₁τ' hreg

end ModularCurve.ComplexPlaceDictionaryOrbit
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff.ModularCurve.ComplexPlaceDictionaryOrbit"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff.ModularCurve"

open ModularCurve.ComplexPlaceDictionaryOrbit in
theorem solution {N : ℕ} [NeZero N]
    (D : ModularCurve.ComplexPlaceDictionary N) (τ τ' : ℍ) :
    D.pt τ = D.pt τ' ↔ ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ = τ' := by
  constructor
  · intro hpt
    by_contra hne
    push Not at hne
    exact pt_ne_pt_of_forall_smul_ne D τ τ' hne hpt
  · rintro ⟨γ, rfl⟩
    exact (D.pt_smul γ τ).symm

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff.ModularCurve.ComplexPlaceDictionaryOrbit"

end S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff (solution)
