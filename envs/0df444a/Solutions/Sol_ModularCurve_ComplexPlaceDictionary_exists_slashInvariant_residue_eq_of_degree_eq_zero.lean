-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_eq_of_degree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4874840e-2f82-5d87-8a8f-4c283e673dc6

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_sum_residue_eq_zero_of_slashInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"

open scoped MatrixGroups Topology ModularForm
open UpperHalfPlane Filter Set

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionary modularFunctionFieldFull laurentBaseChange isCurveOver_laurentBaseChange_modularFunctionFieldFull ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne ComplexPlaceDictionary.sum_residue_eq_zero_of_slashInvariant"
namespace ComplexPlaceDictionary
p2m_export "ModularCurve.ComplexPlaceDictionary" "ramification pt exists_slashInvariant_residue_ne_zero_of_pt_ne sum_residue_eq_zero_of_slashInvariant"
namespace ThirdKindAssembly
p2m_open "ModularCurve.ComplexPlaceDictionary ModularCurve"

def Inv (N : ℕ) (ω : ℍ → ℂ) : Prop := ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ω ∣[(2 : ℤ)] γ = ω

def Cusp (ω : ℍ → ℂ) : Prop :=
  ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
    (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)

def Loc (ω : ℍ → ℂ) (ρ : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = ρ τ / (z - τ) + g z

structure Good (N : ℕ) (ω : ℍ → ℂ) (ρ : ℍ → ℂ) : Prop where
  inv : Inv N ω
  cusp : Cusp ω
  loc : Loc ω ρ

variable {N : ℕ}

theorem exp_isBigO_exp_of_le {δ δ' : ℝ} (h : δ' ≤ δ) :
    (fun τ : ℍ => Real.exp (-δ * τ.im)) =O[atImInfty] fun τ : ℍ => Real.exp (-δ' * τ.im) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, one_mul, Real.exp_le_exp]
  nlinarith [τ.im_pos.le, h]

theorem Good.zero : Good N 0 0 := by
  refine ⟨fun γ _ => SlashAction.zero_slash _ _, fun σ => ⟨1, one_pos, ?_⟩,
    fun τ => ⟨0, analyticAt_const, Eventually.of_forall fun z => by simp⟩⟩
  rw [SlashAction.zero_slash]
  exact Asymptotics.isBigO_zero _ _

theorem Good.add {ω₁ ω₂ ρ₁ ρ₂ : ℍ → ℂ} (h₁ : Good N ω₁ ρ₁) (h₂ : Good N ω₂ ρ₂) :
    Good N (ω₁ + ω₂) (ρ₁ + ρ₂) := by
  refine ⟨fun γ hγ => ?_, fun σ => ?_, fun τ => ?_⟩
  · rw [SlashAction.add_slash, h₁.inv γ hγ, h₂.inv γ hγ]
  · obtain ⟨δ₁, hδ₁, hO₁⟩ := h₁.cusp σ
    obtain ⟨δ₂, hδ₂, hO₂⟩ := h₂.cusp σ
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    rw [SlashAction.add_slash]
    exact (hO₁.trans (exp_isBigO_exp_of_le (min_le_left _ _))).add
      (hO₂.trans (exp_isBigO_exp_of_le (min_le_right _ _)))
  · obtain ⟨g₁, hg₁, he₁⟩ := h₁.loc τ
    obtain ⟨g₂, hg₂, he₂⟩ := h₂.loc τ
    refine ⟨g₁ + g₂, hg₁.add hg₂, ?_⟩
    filter_upwards [he₁, he₂] with z hz₁ hz₂
    simp only [Pi.add_apply, hz₁, hz₂]
    ring

theorem Good.smul {ω ρ : ℍ → ℂ} (h : Good N ω ρ) (a : ℂ) : Good N (a • ω) (a • ρ) := by
  refine ⟨fun γ hγ => ?_, fun σ => ?_, fun τ => ?_⟩
  · rw [ModularForm.SL_smul_slash, h.inv γ hγ]
  · obtain ⟨δ, hδ, hO⟩ := h.cusp σ
    refine ⟨δ, hδ, ?_⟩
    rw [ModularForm.SL_smul_slash]
    exact hO.const_smul_left a
  · obtain ⟨g, hg, he⟩ := h.loc τ
    refine ⟨fun z => a * g z, analyticAt_const.mul hg, ?_⟩
    filter_upwards [he] with z hz
    simp only [Pi.smul_apply, smul_eq_mul, hz]
    ring

theorem Good.congr_res {ω ρ ρ' : ℍ → ℂ} (h : Good N ω ρ) (e : ∀ τ, ρ τ = ρ' τ) : Good N ω ρ' := by
  obtain rfl : ρ = ρ' := funext e
  exact h

theorem Good.sum {ι : Type*} (s : Finset ι) (ω ρ : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, Good N (ω i) (ρ i)) : Good N (∑ i ∈ s, ω i) (∑ i ∈ s, ρ i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using (Good.zero : Good N 0 0)
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (h a (Finset.mem_cons.2 (Or.inl rfl))).add
      (ih fun i hi => h i (Finset.mem_cons.2 (Or.inr hi)))

def μ (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)

theorem μ_coe (g : SL(2, ℤ)) (τ : ℍ) : μ g τ = ((g • τ : ℍ) : ℂ) := by
  simp [μ, ofComplex_apply]

theorem μ_of_im_pos (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    μ g z = ((g • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
  rw [μ, ofComplex_apply_of_im_pos hz]

theorem hasDerivAt_μ (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (μ γ) (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ)) = μ γ := by
    funext z
    rw [μ, MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try first | with_reducible_and_instances rfl | rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem continuousAt_μ (γ : SL(2, ℤ)) (τ : ℍ) : ContinuousAt (μ γ) ↑τ :=
  (hasDerivAt_μ γ τ).continuousAt

theorem slash_two_apply (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) τ =
      f (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) :=
  ModularForm.SL_slash_apply f γ τ

theorem eventually_μ_ne (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), μ γ z ≠ μ γ τ := by
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  filter_upwards [h1, self_mem_nhdsWithin] with z hz hzτ
  rw [μ_of_im_pos γ hz, μ_coe]
  intro h
  have h' : γ • (⟨z, hz⟩ : ℍ) = γ • τ := UpperHalfPlane.ext h
  have h'' := MulAction.injective γ h'
  exact hzτ (congrArg UpperHalfPlane.coe h'')

theorem tendsto_μ_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (μ γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
  rw [← μ_coe]
  refine tendsto_nhdsWithin_iff.mpr
    ⟨(continuousAt_μ γ τ).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  exact eventually_μ_ne γ τ

theorem continuous_denom (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => denom g z) := by
  simp only [denom]
  fun_prop

theorem eventually_im_pos (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
  mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem im_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : (ofComplex z : ℍ).im = z.im := by
  rw [ofComplex_apply_of_im_pos hz]
  rfl

def HasLim (ω : ℍ → ℂ) (τ : ℍ) (L : ℂ) : Prop :=
  Tendsto (fun z : ℂ => ω (ofComplex z)) (𝓝[≠] (τ : ℂ)) (𝓝 L)

open Classical in

def reg (ω : ℍ → ℂ) (τ : ℍ) : ℂ := if h : ∃ L, HasLim ω τ L then h.choose else ω τ

theorem reg_eq_of_hasLim {ω : ℍ → ℂ} {τ : ℍ} {L : ℂ} (h : HasLim ω τ L) : reg ω τ = L := by
  have hex : ∃ L, HasLim ω τ L := ⟨L, h⟩
  rw [reg, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

theorem reg_eq_of_not {ω : ℍ → ℂ} {τ : ℍ} (h : ¬ ∃ L, HasLim ω τ L) : reg ω τ = ω τ := by
  rw [reg, dif_neg h]

theorem hasLim_slash {ω : ℍ → ℂ} (σ : SL(2, ℤ)) (τ : ℍ) {L : ℂ} (h : HasLim ω (σ • τ) L) :
    HasLim (ω ∣[(2 : ℤ)] σ) τ
      (L * denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ)) := by
  have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (ω ∣[(2 : ℤ)] σ) (ofComplex z) =
      ω (ofComplex (μ σ z)) * denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) z ^ (-2 : ℤ) := by
    filter_upwards [eventually_im_pos τ] with z hz
    rw [slash_two_apply, ofComplex_apply_of_im_pos hz, μ_of_im_pos σ hz, ofComplex_apply]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  refine (h.comp (tendsto_μ_nhdsNE σ τ)).mul ?_
  exact (((continuous_denom _).continuousAt.zpow₀ _ (Or.inl (denom_ne_zero _ τ))).tendsto).mono_left
    nhdsWithin_le_nhds

theorem inv_reg {ω : ℍ → ℂ} (hω : Inv N ω) : Inv N (reg ω) := by
  intro γ hγ
  funext τ
  rw [slash_two_apply]
  by_cases h : ∃ L, HasLim ω (γ • τ) L
  · obtain ⟨L, hL⟩ := h
    have h1 : HasLim ω τ (L * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) := by
      have := hasLim_slash γ τ hL
      rwa [hω γ hγ] at this
    rw [reg_eq_of_hasLim hL, reg_eq_of_hasLim h1]
  · have h' : ¬ ∃ L, HasLim ω τ L := by
      rintro ⟨L, hL⟩
      apply h
      have hL' : HasLim ω (γ⁻¹ • (γ • τ)) L := by rwa [inv_smul_smul]
      have := hasLim_slash γ⁻¹ (γ • τ) hL'
      rw [hω γ⁻¹ (Subgroup.inv_mem _ hγ)] at this
      exact ⟨_, this⟩
    rw [reg_eq_of_not h, reg_eq_of_not h', ← slash_two_apply, hω γ hγ]

theorem cusp_reg {ω : ℍ → ℂ} (hω : Cusp ω) : Cusp (reg ω) := by
  intro σ
  obtain ⟨δ, hδ, hO⟩ := hω σ
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine ⟨δ, hδ, Asymptotics.IsBigO.of_bound C ?_⟩
  rw [Filter.Eventually, atImInfty_mem]
  refine ⟨A + 1, fun τ hτ => ?_⟩
  have hAτ : A < τ.im := by linarith
  show ‖(reg ω ∣[(2 : ℤ)] σ) τ‖ ≤ C * ‖Real.exp (-δ * τ.im)‖
  rw [slash_two_apply]
  by_cases h : ∃ L, HasLim ω (σ • τ) L
  · obtain ⟨L, hL⟩ := h
    rw [reg_eq_of_hasLim hL]
    have hlim := hasLim_slash σ τ hL
    have hf : Tendsto (fun z => ‖(ω ∣[(2 : ℤ)] σ) (ofComplex z)‖) (𝓝[≠] (τ : ℂ))
        (𝓝 ‖L * denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ)‖) := hlim.norm
    have hc : Continuous fun z : ℂ => C * ‖Real.exp (-δ * z.im)‖ := by fun_prop
    have hg : Tendsto (fun z : ℂ => C * ‖Real.exp (-δ * (ofComplex z : ℍ).im)‖) (𝓝[≠] (τ : ℂ))
        (𝓝 (C * ‖Real.exp (-δ * τ.im)‖)) := by
      refine ((hc.tendsto (τ : ℂ)).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [eventually_im_pos τ] with z hz
      rw [im_ofComplex_of_im_pos hz]
    refine le_of_tendsto_of_tendsto hf hg ?_
    have hopen : IsOpen {z : ℂ | A < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [eventually_im_pos τ, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hAτ)]
      with z hz hzA
    exact hA (ofComplex z) (by rw [im_ofComplex_of_im_pos hz]; exact le_of_lt hzA)
  · rw [reg_eq_of_not h, ← slash_two_apply]
    exact hA τ hAτ.le

theorem reg_ofComplex_eventuallyEq {ω : ℍ → ℂ} {τ : ℍ} {a : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g τ)
    (he : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = a / (z - τ) + g z) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), reg ω (ofComplex z) = ω (ofComplex z) := by
  have h1 : ∀ᶠ z in 𝓝 (τ : ℂ), AnalyticAt ℂ g z := hg.eventually_analyticAt
  have h2 : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ᶠ w in 𝓝 z, w ≠ (τ : ℂ) → ω (ofComplex w) = a / (w - τ) + g w :=
    (eventually_nhdsWithin_iff.mp he).eventually_nhds
  have h3 : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im := isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3 hzτ
  apply reg_eq_of_hasLim
  have hF : ContinuousAt (fun w => a / (w - τ) + g w) z :=
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hzτ)).add
      hz1.continuousAt
  have hev : (fun w => ω (ofComplex w)) =ᶠ[𝓝 z] fun w => a / (w - τ) + g w := by
    filter_upwards [hz2, isOpen_ne.mem_nhds hzτ] with w hw hwτ
    exact hw hwτ
  have hlim : Tendsto (fun w => ω (ofComplex w)) (𝓝 z) (𝓝 (ω (ofComplex z))) := by
    rw [show ω (ofComplex z) = a / (z - τ) + g z from hev.self_of_nhds]
    exact hF.tendsto.congr' hev.symm
  show Tendsto _ (𝓝[≠] ((ofComplex z : ℍ) : ℂ)) _
  rw [coe_ofComplex_of_im_pos hz3]
  exact hlim.mono_left nhdsWithin_le_nhds

theorem loc_reg {ω ρ : ℍ → ℂ} (h : Loc ω ρ) (τ : ℍ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g τ ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), reg ω (ofComplex z) = ρ τ / (z - τ) + g z) ∧
      (ρ τ = 0 → reg ω τ = g τ) := by
  obtain ⟨g, hg, he⟩ := h τ
  refine ⟨g, hg, ?_, fun h0 => ?_⟩
  · filter_upwards [reg_ofComplex_eventuallyEq hg he, he] with z h1 h2
    rw [h1, h2]
  · apply reg_eq_of_hasLim
    have hev : (fun z => ω (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] g := by
      filter_upwards [he] with z hz
      rw [hz, h0, zero_div, zero_add]
    exact ((hg.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' hev.symm

abbrev Pl (N : ℕ) [NeZero N] : Type _ :=
  AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))

variable [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N)

def Res (d : Pl N →₀ ℂ) (τ : ℍ) : ℂ := (D.ramification τ : ℂ) * d (D.pt τ)

theorem finsupp_eq_sum_smul_single_sub {α : Type*} [DecidableEq α] (d : α →₀ ℂ) {Q : α}
    (hQ : Q ∈ d.support) (hsum : d.sum (fun _ a => a) = 0) :
    ∑ v ∈ d.support.erase Q, d v • (Finsupp.single v (1 : ℂ) - Finsupp.single Q 1) = d := by
  have hS : ∑ v ∈ d.support.erase Q, d v = -d Q := by
    rw [Finset.sum_erase_eq_sub hQ]
    change d.sum (fun _ a => a) - d Q = -d Q
    rw [hsum, zero_sub]
  ext w
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, Finsupp.coe_sub, Pi.sub_apply, smul_eq_mul,
    Finsupp.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (d.support.erase Q) w (fun v => d v), Finset.sum_ite_irrel,
    Finset.sum_const_zero, hS]
  by_cases hQw : Q = w
  · subst hQw
    simp
  · rw [if_neg hQw, sub_zero]
    by_cases hw : w ∈ d.support
    · rw [if_pos (Finset.mem_erase.2 ⟨Ne.symm hQw, hw⟩)]
    · rw [if_neg (fun h => hw (Finset.mem_of_mem_erase h)), eq_comm]
      exact Finsupp.notMem_support_iff.mp hw

variable {D} in
theorem Res_finset_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → Pl N →₀ ℂ) (τ : ℍ) :
    (∑ i ∈ s, a i • Res D (f i)) τ = Res D (∑ i ∈ s, a i • f i) τ := by
  simp only [Res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_good_twoPoint {τ₁ τ₂ : ℍ} (hne : D.pt τ₁ ≠ D.pt τ₂) :
    ∃ ω : ℍ → ℂ, Good N ω
      (Res D (Finsupp.single (D.pt τ₁) 1 - Finsupp.single (D.pt τ₂) 1)) := by
  classical
  obtain ⟨ω₀, r, hinv, hcusp, hr₁, hsupp, hloc⟩ :=
    ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne D hne

  have hsum : r.sum (fun _ a => a) = 0 := by
    refine ModularCurve.ComplexPlaceDictionary.sum_residue_eq_zero_of_slashInvariant D ω₀ r hinv
      hcusp (fun P hP => ?_) hloc
    rcases hsupp P (Finsupp.mem_support_iff.mp hP) with h | h
    · exact ⟨τ₁, h.symm⟩
    · exact ⟨τ₂, h.symm⟩
  have hPQ : r.sum (fun _ a => a) = r (D.pt τ₁) + r (D.pt τ₂) := by
    rw [Finsupp.sum_of_support_subset r (s := {D.pt τ₁, D.pt τ₂}) ?_ _ (fun _ _ => rfl)]
    · exact Finset.sum_pair hne
    · intro P hP
      rcases hsupp P (Finsupp.mem_support_iff.mp hP) with h | h <;> simp [h]
  set a := r (D.pt τ₁) with ha
  have hr₂ : r (D.pt τ₂) = -a := by
    rw [hPQ] at hsum
    linear_combination hsum
  have hr0 : ∀ τ, D.pt τ ≠ D.pt τ₁ → D.pt τ ≠ D.pt τ₂ → r (D.pt τ) = 0 := by
    intro τ h1 h2
    by_contra h
    rcases hsupp _ h with h' | h'
    · exact h1 h'
    · exact h2 h'
  have hgood : Good N ω₀ (Res D r) := ⟨hinv, hcusp, hloc⟩
  refine ⟨a⁻¹ • ω₀, (hgood.smul a⁻¹).congr_res fun τ => ?_⟩
  simp only [Res, Pi.smul_apply, smul_eq_mul, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
  by_cases h₁ : D.pt τ₁ = D.pt τ
  · have h₂ : D.pt τ₂ ≠ D.pt τ := fun h => hne (h₁.trans h.symm)
    rw [if_pos h₁, if_neg h₂, ← h₁, ← ha]
    field_simp
    ring
  · rw [if_neg h₁]
    by_cases h₂ : D.pt τ₂ = D.pt τ
    · rw [if_pos h₂, ← h₂, hr₂]
      field_simp
      ring
    · rw [if_neg h₂, hr0 τ (Ne.symm h₁) (Ne.symm h₂)]
      ring

theorem exists_good_of_sum_eq_zero (d : Pl N →₀ ℂ) (hsupp : ∀ v ∈ d.support, ∃ τ : ℍ, D.pt τ = v)
    (hsum : d.sum (fun _ a => a) = 0) : ∃ ω : ℍ → ℂ, Good N ω (Res D d) := by
  classical
  by_cases h0 : d = 0
  · subst h0
    exact ⟨0, Good.zero.congr_res fun τ => by simp [Res]⟩
  obtain ⟨Q, hQ⟩ := Finsupp.support_nonempty_iff.mpr h0
  obtain ⟨τQ, hτQ⟩ := hsupp Q hQ
  subst hτQ
  have key : ∀ v ∈ d.support.erase (D.pt τQ), ∃ ω : ℍ → ℂ,
      Good N ω (Res D (Finsupp.single v 1 - Finsupp.single (D.pt τQ) 1)) := by
    intro v hv
    obtain ⟨hvQ, hvS⟩ := Finset.mem_erase.mp hv
    obtain ⟨τv, hτv⟩ := hsupp v hvS
    subst hτv
    exact exists_good_twoPoint D hvQ
  choose! ωv hωv using key
  refine ⟨∑ v ∈ d.support.erase (D.pt τQ), d v • ωv v, ?_⟩
  have hG := Good.sum (N := N) (d.support.erase (D.pt τQ)) (fun v => d v • ωv v)
    (fun v => d v • Res D (Finsupp.single v 1 - Finsupp.single (D.pt τQ) 1))
    fun v hv => (hωv v hv).smul (d v)
  refine hG.congr_res fun τ => ?_
  rw [Res_finset_sum_smul, finsupp_eq_sum_smul_single_sub d hQ hsum]

theorem sum_eq_zero_of_degree_eq_zero
    (d₀ : AlgebraicCurve.Divisor ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
    (hdeg : AlgebraicCurve.Divisor.degree d₀ = 0) : d₀.sum (fun _ n => n) = 0 := by
  haveI := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N
  have h1 : AlgebraicCurve.Divisor.degree d₀ = d₀.sum fun v n => n * (v.deg : ℤ) := by
    rw [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply]
    rfl
  rw [h1] at hdeg
  simpa [AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed] using hdeg

end ModularCurve.ComplexPlaceDictionary.ThirdKindAssembly

end

open ModularCurve.ComplexPlaceDictionary.ThirdKindAssembly in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ ω : ℍ → ℂ,
      (∀ γ ∈ CongruenceSubgroup.Gamma0 N, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : ℂ) / (z - τ) + g z) ∧
        ((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) = 0 → ω τ = g τ) := by
  classical
  set d₀ := Finsupp.mapDomain D.pt c with hd₀
  let d : Pl N →₀ ℂ := Finsupp.mapRange (fun n : ℤ => (n : ℂ)) Int.cast_zero d₀
  have hd_apply : ∀ v, d v = (d₀ v : ℂ) := fun v => Finsupp.mapRange_apply ..
  have hsupp : ∀ v ∈ d.support, ∃ τ : ℍ, D.pt τ = v := by
    intro v hv
    have hv' : v ∈ d₀.support := Finsupp.support_mapRange hv
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv')
    exact ⟨τ, rfl⟩
  have hsum : d.sum (fun _ a => a) = 0 := by
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    have h1 : (d₀.sum fun _ n => ((n : ℤ) : ℂ)) = ((d₀.sum fun _ n => n : ℤ) : ℂ) := by
      simp [Finsupp.sum]
    rw [h1, sum_eq_zero_of_degree_eq_zero d₀ hdeg, Int.cast_zero]
  obtain ⟨ω, hω⟩ := exists_good_of_sum_eq_zero D d hsupp hsum
  refine ⟨reg ω, inv_reg hω.inv, cusp_reg hω.cusp, fun τ => ?_⟩
  obtain ⟨g, hg, he, hv⟩ := loc_reg hω.loc τ
  have hres : Res D d τ = (((D.ramification τ : ℤ) * d₀ (D.pt τ) : ℤ) : ℂ) := by
    simp only [Res, hd_apply]
    push_cast
    ring
  refine ⟨g, hg, ?_, fun h0 => hv ?_⟩
  · filter_upwards [he] with z hz
    rw [hz, hres]
  · rw [hres, h0, Int.cast_zero]

end S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero (solution)
