-- Prove2me | solution 1 for ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6514912c-7030-54a7-a07d-fa99e410b631

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
import Theorems.Thm_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_JZero_exists_regVal_chord_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace ConfLedger

open AlgebraicCurve

namespace Sum

section Sup

theorem iSup_pos_of_exists {L Φ : Type*} {ι : Type*} [Finite ι] [FunLike Φ L ℝ] (ν : Φ) (z : ι → L)
    (h : ∃ i, 0 < ν (z i)) : 0 < ⨆ i, ν (z i) := by
  obtain ⟨i, hi⟩ := h
  exact lt_of_lt_of_le hi (Finite.le_ciSup_of_le i le_rfl)

theorem iSup_apply_zero {L Φ : Type*} {ι : Type*} [FunLike Φ L ℝ] [Zero L] [ZeroHomClass Φ L ℝ] (ν : Φ) :
    (⨆ _ : ι, ν (0 : L)) = 0 := by
  simp only [map_zero, Real.iSup_const_zero]

end Sup

section AbsHeight

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

theorem absLogHeight_zero {ι : Type} [Fintype ι] :
    absLogHeight (0 : ι → AlgebraicClosure ℚ) = 0 := by
  haveI := finiteDimensional_adjoin_range (0 : ι → AlgebraicClosure ℚ)
  unfold AlgebraicCurve.absLogHeight
  have h0 : (fun i => (⟨(0 : ι → AlgebraicClosure ℚ) i,
      IntermediateField.subset_adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)))) = 0 := by
    funext i
    exact Subtype.ext rfl
  rw [h0, Height.logHeight_zero, mul_zero]

end AbsHeight

section Places

open NumberField

variable {M : Type*} [Field M] [NumberField M]

theorem hfms_iSup {ι : Type*} [Finite ι] {x : ι → M} (hx : x ≠ 0) :
    (fun v : FinitePlace M ↦ ⨆ i, v (x i)).HasFiniteMulSupport := by
  obtain ⟨i₀, hi₀⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i₀
  have hne : Nonempty {j // x j ≠ 0} := ⟨⟨i₀, hi₀⟩⟩
  have key : ∀ v : FinitePlace M, (⨆ i, v (x i)) = ⨆ i : {j // x j ≠ 0}, v (x i.val) := by
    intro v
    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun j ↦ Finite.le_ciSup_of_le j.val le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, map_zero]
      exact Real.iSup_nonneg fun i ↦ apply_nonneg v _
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  have heq : (fun v : FinitePlace M ↦ ⨆ i, v (x i)) =
      fun v : FinitePlace M ↦ ⨆ i : {j // x j ≠ 0}, v (x i.val) := funext key
  rw [heq]
  exact Function.HasFiniteMulSupport.iSup fun i ↦ FinitePlace.hasFiniteMulSupport i.prop

theorem iSup_pos_fin {ι : Type*} [Finite ι] (v : FinitePlace M) {z : ι → M} (hz : z ≠ 0) :
    0 < ⨆ i, v (z i) := by
  obtain ⟨i, hi⟩ : ∃ j, z j ≠ 0 := Function.ne_iff.mp hz
  exact iSup_pos_of_exists v z ⟨i, FinitePlace.pos_iff.mpr hi⟩

omit [NumberField M] in
theorem iSup_pos_inf {ι : Type*} [Finite ι] (w : InfinitePlace M) {z : ι → M} (hz : z ≠ 0) :
    0 < ⨆ i, w (z i) := by
  obtain ⟨i, hi⟩ : ∃ j, z j ≠ 0 := Function.ne_iff.mp hz
  exact iSup_pos_of_exists w z ⟨i, InfinitePlace.pos_iff.mpr hi⟩

open Classical in

def vsupp {ι : Type*} [Finite ι] (z : ι → M) : Finset (FinitePlace M) :=
  if h : z = 0 then ∅ else (hfms_iSup h).toFinset

theorem vsupp_spec {ι : Type*} [Finite ι] (z : ι → M) (h : z ≠ 0) :
    Function.mulSupport (fun v : FinitePlace M => ⨆ i, v (z i)) ⊆ ↑(vsupp z) := by
  rw [vsupp, dif_neg h, Set.Finite.coe_toFinset]

open Classical in

def csupp (c : M) : Finset (FinitePlace M) :=
  if h : c = 0 then ∅ else (FinitePlace.hasFiniteMulSupport h).toFinset

theorem csupp_spec (c : M) (h : c ≠ 0) :
    Function.mulSupport (fun v : FinitePlace M => v c) ⊆ ↑(csupp c) := by
  rw [csupp, dif_neg h, Set.Finite.coe_toFinset]

def PSL (T : Finset (FinitePlace M)) : ((M → ℝ) → ℝ) →ₗ[ℝ] ℝ where
  toFun g := (∑ w : InfinitePlace M, (w.mult : ℝ) * g w) + ∑ v ∈ T, g v
  map_add' g₁ g₂ := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c g := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem PSL_apply (T : Finset (FinitePlace M)) (g : (M → ℝ) → ℝ) :
    PSL T g = (∑ w : InfinitePlace M, (w.mult : ℝ) * g w) + ∑ v ∈ T, g v := rfl

def La {ι : Type*} (z : ι → M) : (M → ℝ) → ℝ := fun ν => Real.log (⨆ i, ν (z i))

def Lc (c : M) : (M → ℝ) → ℝ := fun ν => Real.log (ν c)

omit [Field M] [NumberField M] in
theorem La_apply {ι : Type*} (z : ι → M) (ν : M → ℝ) : La z ν = Real.log (⨆ i, ν (z i)) := rfl

omit [Field M] [NumberField M] in
theorem Lc_apply (c : M) (ν : M → ℝ) : Lc c ν = Real.log (ν c) := rfl

theorem PSL_Lc (T : Finset (FinitePlace M)) (c : M)
    (hT : c ≠ 0 → Function.mulSupport (fun v : FinitePlace M => v c) ⊆ ↑T) :
    PSL T (Lc c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [PSL_apply, Lc, map_zero, Real.log_zero]
  have hpf := NumberField.prod_abs_eq_one (K := M) hc
  rw [finprod_eq_prod_of_mulSupport_subset _ (hT hc)] at hpf
  have hlog := congrArg Real.log hpf
  rw [Real.log_one, Real.log_mul, Real.log_prod, Real.log_prod] at hlog
  · rw [PSL_apply]
    simp only [Lc]
    simpa only [Real.log_pow] using hlog
  · intro v _; exact (FinitePlace.pos_iff.mpr hc).ne'
  · intro w _; exact pow_ne_zero _ (InfinitePlace.pos_iff.mpr hc).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (InfinitePlace.pos_iff.mpr hc).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun v _ => (FinitePlace.pos_iff.mpr hc).ne'

theorem sum_neg_log_natCast (T : Finset (FinitePlace M)) (p : ℕ) (hp : p ≠ 0)
    (hT : Function.mulSupport (fun v : FinitePlace M => v (p : M)) ⊆ ↑T) :
    ∑ v ∈ T, -Real.log (v (p : M)) = (Module.finrank ℚ M : ℝ) * Real.log p := by
  have hp' : (p : M) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h := PSL_Lc T (p : M) (fun _ => hT)
  rw [PSL_apply] at h
  have hw : ∀ w : InfinitePlace M, w (p : M) = p := fun w => by simp
  simp only [Lc, hw] at h
  rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq] at h
  rw [Finset.sum_neg_distrib]
  linarith

theorem natCast_le_one (v : FinitePlace M) (p : ℕ) : v (p : M) ≤ 1 := by
  have := NumberField.FinitePlace.norm_le_one (K := M) v.maximalIdeal (p : 𝓞 M)
  rwa [NumberField.FinitePlace.norm_embedding_eq, map_natCast] at this

theorem neg_log_natCast_nonneg (v : FinitePlace M) (p : ℕ) (hp : p ≠ 0) : 0 ≤ -Real.log (v (p : M)) := by
  rw [neg_nonneg]
  exact Real.log_nonpos (apply_nonneg v _) (natCast_le_one v p)

theorem abs_PSL_le (T : Finset (FinitePlace M)) (g : (M → ℝ) → ℝ) (a : ℝ) (h : FinitePlace M → ℝ)
    (hinf : ∀ w : InfinitePlace M, |g w| ≤ a) (hfin : ∀ v ∈ T, |g v| ≤ h v) :
    |PSL T g| ≤ (Module.finrank ℚ M : ℝ) * a + ∑ v ∈ T, h v := by
  rw [PSL_apply]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : InfinitePlace M, |(w.mult : ℝ) * g w|
        ≤ ∑ w : InfinitePlace M, (w.mult : ℝ) * a := Finset.sum_le_sum fun w _ => by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hinf w) (Nat.cast_nonneg _)
      _ = (Module.finrank ℚ M : ℝ) * a := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hfin)

end Places

section Bridge

open NumberField

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]

theorem PSL_La {ι : Type} [Fintype ι] (z : ι → ↥L) (T : Finset (FinitePlace ↥L))
    (hT : z ≠ 0 → Function.mulSupport (fun v : FinitePlace ↥L => ⨆ i, v (z i)) ⊆ ↑T) :
    PSL T (La z) = (Module.finrank ℚ ↥L : ℝ) * absLogHeight (fun i => ((z i : ↥L) : AlgebraicClosure ℚ)) := by
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · have h1 : (fun i => (((0 : ι → ↥L) i : ↥L) : AlgebraicClosure ℚ)) = 0 := by
      funext i; rfl
    rw [h1, absLogHeight_zero, mul_zero, PSL_apply]
    simp [La, map_zero, Real.iSup_const_zero, Real.log_zero]
  have hmem : ∀ i, ((z i : ↥L) : AlgebraicClosure ℚ) ∈ L := fun i => (z i).2
  rw [absLogHeight_eq_of_mem _ L hmem]
  have hz' : (fun i => (⟨((z i : ↥L) : AlgebraicClosure ℚ), hmem i⟩ : ↥L)) = z := by
    funext i; rfl
  have hd : (Module.finrank ℚ ↥L : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ ↥L := Module.finrank_pos
    exact_mod_cast this.ne'
  rw [hz', ← mul_assoc, mul_inv_cancel₀ hd, one_mul, Height.logHeight_eq_log_mulHeight,
    NumberField.mulHeight_eq hz, finprod_eq_prod_of_mulSupport_subset _ (hT hz), Real.log_mul, Real.log_prod,
    Real.log_prod, PSL_apply]
  · simp only [La, Real.log_pow]
  · intro v _; exact (iSup_pos_fin v hz).ne'
  · intro w _; exact pow_ne_zero _ (iSup_pos_inf w hz).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (iSup_pos_inf w hz).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun v _ => (iSup_pos_fin v hz).ne'

def lineF {α : Type*} {r : ℕ} (x : α → Fin r → ↥L) (o : α) (S₀ : Finset α) (β : α → ℝ) (κ e : ℝ)
    (yy : Fin r × Fin r → ↥L) (cc : ↥L) : (↥L → ℝ) → ℝ :=
  (∑ w ∈ S₀, β w • (La (x o) + La (x w) - La (fun q : Fin r × Fin r => x o q.1 * x w q.2 - x o q.2 * x w q.1)))
    - (κ • La (x o) + e • La yy - Lc cc)

omit [FiniteDimensional ℚ L] in
theorem lineF_apply {α : Type*} {r : ℕ} (x : α → Fin r → ↥L) (o : α) (S₀ : Finset α) (β : α → ℝ) (κ e : ℝ)
    (yy : Fin r × Fin r → ↥L) (cc : ↥L) (ν : ↥L → ℝ) :
    lineF L x o S₀ β κ e yy cc ν
      = (∑ w ∈ S₀, β w * prox ν (x o) (x w))
        - (κ * Real.log (⨆ i, ν (x o i)) + e * Real.log (⨆ q, ν (yy q)) - Real.log (ν cc)) := by
  simp only [lineF, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, La, Lc, prox]

theorem PSL_lineF {α : Type*} {r : ℕ} (T : Finset (FinitePlace ↥L)) (x : α → Fin r → ↥L) (o : α)
    (S₀ : Finset α) (β : α → ℝ) (κ e : ℝ) (yy : Fin r × Fin r → ↥L) (cc : ↥L)
    (hx : ∀ w, w = o ∨ w ∈ S₀ → x w ≠ 0 →
      Function.mulSupport (fun v : FinitePlace ↥L => ⨆ i, v (x w i)) ⊆ ↑T)
    (hmn : ∀ w ∈ S₀, (fun q : Fin r × Fin r => x o q.1 * x w q.2 - x o q.2 * x w q.1) ≠ 0 →
      Function.mulSupport (fun v : FinitePlace ↥L =>
        ⨆ q : Fin r × Fin r, v (x o q.1 * x w q.2 - x o q.2 * x w q.1)) ⊆ ↑T)
    (hyy : yy ≠ 0 → Function.mulSupport (fun v : FinitePlace ↥L => ⨆ q, v (yy q)) ⊆ ↑T)
    (hcc : cc ≠ 0 → Function.mulSupport (fun v : FinitePlace ↥L => v cc) ⊆ ↑T) :
    PSL T (lineF L x o S₀ β κ e yy cc)
      = (Module.finrank ℚ ↥L : ℝ) *
        ((∑ w ∈ S₀, β w * (absLogHeight (fun i => ((x o i : ↥L) : AlgebraicClosure ℚ))
            + absLogHeight (fun i => ((x w i : ↥L) : AlgebraicClosure ℚ))
            - absLogHeight (fun q : Fin r × Fin r =>
                (((x o q.1 * x w q.2 - x o q.2 * x w q.1 : ↥L)) : AlgebraicClosure ℚ))))
          - (κ * absLogHeight (fun i => ((x o i : ↥L) : AlgebraicClosure ℚ))
              + e * absLogHeight (fun q => ((yy q : ↥L) : AlgebraicClosure ℚ)))) := by
  have ho := PSL_La L (x o) T (hx o (Or.inl rfl))
  have hterm : ∀ w ∈ S₀,
      PSL T (β w • (La (x o) + La (x w) - La (fun q : Fin r × Fin r => x o q.1 * x w q.2 - x o q.2 * x w q.1)))
        = (Module.finrank ℚ ↥L : ℝ) * (β w * (absLogHeight (fun i => ((x o i : ↥L) : AlgebraicClosure ℚ))
            + absLogHeight (fun i => ((x w i : ↥L) : AlgebraicClosure ℚ))
            - absLogHeight (fun q : Fin r × Fin r =>
                (((x o q.1 * x w q.2 - x o q.2 * x w q.1 : ↥L)) : AlgebraicClosure ℚ)))) := by
    intro w hw
    rw [LinearMap.map_smul, map_sub, map_add, ho, PSL_La L (x w) T (hx w (Or.inr hw)),
      PSL_La L (fun q : Fin r × Fin r => x o q.1 * x w q.2 - x o q.2 * x w q.1) T (hmn w hw), smul_eq_mul]
    ring
  rw [lineF, map_sub, map_sum, map_sub, map_add, LinearMap.map_smul, LinearMap.map_smul, PSL_Lc T cc hcc,
    ho, PSL_La L yy T hyy, Finset.sum_congr rfl hterm, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
  ring

end Bridge

section PlacesExtra
open NumberField
variable {M : Type*} [Field M] [NumberField M]

theorem PSL_le (T : Finset (FinitePlace M)) (g : (M → ℝ) → ℝ) (a : ℝ) (h : FinitePlace M → ℝ)
    (hinf : ∀ w : InfinitePlace M, g w ≤ a) (hfin : ∀ v ∈ T, g v ≤ h v) :
    PSL T g ≤ (Module.finrank ℚ M : ℝ) * a + ∑ v ∈ T, h v := by
  rw [PSL_apply]
  refine add_le_add ?_ (Finset.sum_le_sum hfin)
  calc ∑ w : InfinitePlace M, (w.mult : ℝ) * g w
      ≤ ∑ w : InfinitePlace M, (w.mult : ℝ) * a :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hinf w) (Nat.cast_nonneg _)
    _ = (Module.finrank ℚ M : ℝ) * a := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
end PlacesExtra

end Sum

namespace Alg

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero' (v : Place K F) : v.evalAt (0 : F) = 0 := by
  have h := Place.evalAt_algebraMap v (0 : K)
  rwa [map_zero] at h

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem smul_mem_toValuationSubring (v : Place K F) (a : K) {f : F}
    (hf : f ∈ v.toValuationSubring) : a • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (v : Place K F) (hv : v.IsRational) (a : K) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, Place.evalAt_mul v hv (v.algebraMap_mem' a) hf, Place.evalAt_algebraMap]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := v.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (v.adicValuation f))
  omega

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f = 0) : 0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf0 hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (Place.evalAt_ne_zero v hv hf0 heq.symm)

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (ord_nonneg_of_mem v hf0 hf) (Ne.symm hne)

  apply h
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    omega
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hf, map_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem

theorem evalAt_sum_smul (v : Place K F) (hv : v.IsRational)
    {ι : Type*} (T : Finset ι) (a : ι → K) (f : ι → F)
    (hf : ∀ j ∈ T, f j ∈ v.toValuationSubring) :
    v.evalAt (∑ j ∈ T, a j • f j) = ∑ j ∈ T, a j * v.evalAt (f j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [evalAt_zero' v]
  | @insert j T hj ih =>
    have hfT : ∀ j' ∈ T, f j' ∈ v.toValuationSubring :=
      fun j' hj' => hf j' (Finset.mem_insert_of_mem hj')
    have hfj : f j ∈ v.toValuationSubring := hf j (Finset.mem_insert_self j T)
    have hsum : (∑ j' ∈ T, a j' • f j') ∈ v.toValuationSubring :=
      sum_mem fun j' hj' => smul_mem_toValuationSubring v (a j') (hfT j' hj')
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      evalAt_add_of_mem v hv (smul_mem_toValuationSubring v (a j) hfj) hsum,
      evalAt_smul_of_mem v hv (a j) hfj, ih hfT]

theorem taylorCoeff_sum_smul (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {ι : Type*} (T : Finset ι) (a : ι → K) (f : ι → F)
    (hf : ∀ j ∈ T, f j ∈ v.toValuationSubring) (r : ℕ) :
    Place.taylorCoeff v t r (∑ j ∈ T, a j • f j) = ∑ j ∈ T, a j * Place.taylorCoeff v t r (f j) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := Place.taylorCoeff_smul v hv ht (f := (0 : F)) (zero_mem _) (0 : K) r
    simpa using h
  | @insert j T hj ih =>
    have hfT : ∀ j' ∈ T, f j' ∈ v.toValuationSubring :=
      fun j' hj' => hf j' (Finset.mem_insert_of_mem hj')
    have hfj : f j ∈ v.toValuationSubring := hf j (Finset.mem_insert_self j T)
    have hsum : (∑ j' ∈ T, a j' • f j') ∈ v.toValuationSubring :=
      sum_mem fun j' hj' => smul_mem_toValuationSubring v (a j') (hfT j' hj')
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      Place.taylorCoeff_add v hv ht (smul_mem_toValuationSubring v (a j) hfj) hsum r,
      Place.taylorCoeff_smul v hv ht hfj (a j) r, ih hfT]

theorem taylorCoeff_sum_smul' (v : Place K F) (hv : v.IsRational) {t : F} {r : ℕ}
    (ht : 0 < r → v.ord t = 1) {ι : Type*} (T : Finset ι) (a : ι → K) (f : ι → F)
    (hf : ∀ j ∈ T, f j ∈ v.toValuationSubring) :
    Place.taylorCoeff v t r (∑ j ∈ T, a j • f j) = ∑ j ∈ T, a j * Place.taylorCoeff v t r (f j) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp only [Place.taylorCoeff_zero]
    exact evalAt_sum_smul v hv T a f hf
  · exact taylorCoeff_sum_smul v hv (ht hr) T a f hf r

variable {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ) (u : Fin M → F)

noncomputable def cofSec (i₀ : Fin M) : F :=
  ∑ j, (jetMatrix P t e u).adjugate j i₀ • u j

theorem cofSec_def (i₀ : Fin M) :
    cofSec P t e u i₀ = ∑ j, (jetMatrix P t e u).adjugate j i₀ • u j := rfl

theorem cofSec_mem_submodule {V : Submodule K F} (huV : ∀ j, u j ∈ V) (i₀ : Fin M) :
    cofSec P t e u i₀ ∈ V :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (huV j)

theorem cofSec_mem_toValuationSubring (v : Place K F) (huv : ∀ j, u j ∈ v.toValuationSubring)
    (i₀ : Fin M) : cofSec P t e u i₀ ∈ v.toValuationSubring :=
  sum_mem fun j _ => smul_mem_toValuationSubring v _ (huv j)

theorem taylorCoeff_cofSec (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, 0 < e i → (P i).ord (t i) = 1)
    (hu : ∀ i j, u j ∈ (P i).toValuationSubring) (i₀ i : Fin M) :
    (P i).taylorCoeff (t i) (e i) (cofSec P t e u i₀)
      = if i = i₀ then (jetMatrix P t e u).det else 0 := by
  classical
  rw [cofSec_def, taylorCoeff_sum_smul' (P i) (hrat i) (hord i) Finset.univ _ _ (fun j _ => hu i j)]
  have h := congrFun (congrFun (Matrix.mul_adjugate (jetMatrix P t e u)) i) i₀
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, jetMatrix_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem cofSec_ne_zero (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, 0 < e i → (P i).ord (t i) = 1)
    (hu : ∀ i j, u j ∈ (P i).toValuationSubring) (i₀ : Fin M)
    (hdet : (jetMatrix P t e u).det ≠ 0) : cofSec P t e u i₀ ≠ 0 := by
  intro h0
  have h := taylorCoeff_cofSec P t e u hrat hord hu i₀ i₀
  rw [if_pos rfl, h0] at h

  have hz := taylorCoeff_sum_smul' (P i₀) (hrat i₀) (hord i₀) (∅ : Finset (Fin 1))
    (fun _ => (0 : K)) (fun _ => (0 : F)) (fun _ h => absurd h (Finset.notMem_empty _))
  simp only [Finset.sum_empty] at hz
  exact hdet (h.symm.trans hz)

def IsTopRow (i₀ : Fin M) : Prop := ∀ i, P i = P i₀ → e i ≤ e i₀

theorem exists_isTopRow (S : Finset (Fin M)) (hS : S.Nonempty)
    (hblock : ∀ i ∈ S, ∀ i', P i' = P i → i' ∈ S) : ∃ i₀ ∈ S, IsTopRow P e i₀ := by
  classical
  obtain ⟨i, hi⟩ := hS
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (S.filter fun i' => P i' = P i) e
    ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  rw [Finset.mem_filter] at hi₀
  refine ⟨i₀, hi₀.1, fun i' hi' => hmax i' (Finset.mem_filter.mpr ⟨?_, ?_⟩)⟩
  · exact hblock i₀ hi₀.1 i' hi'
  · rw [hi', hi₀.2]

theorem taylorCoeff_cofSec_eq_zero_of_lt (hpat : IsConfluentPattern P t e)
    (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, 0 < e i → (P i).ord (t i) = 1)
    (hu : ∀ i j, u j ∈ (P i).toValuationSubring) (i₀ : Fin M)
    (q : ℕ) (hq : q < e i₀) : (P i₀).taylorCoeff (t i₀) q (cofSec P t e u i₀) = 0 := by
  obtain ⟨i', hP, he⟩ := hpat.exists_eq_of_lt_jetMult i₀ (lt_trans hq (hpat.2.2 i₀))
  have ht : t i' = t i₀ := hpat.1 i' i₀ hP
  have hne : i' ≠ i₀ := by rintro rfl; omega
  have h := taylorCoeff_cofSec P t e u hrat hord hu i₀ i'
  rw [if_neg hne, hP, ht, he] at h
  exact h

theorem evalAt_cofSec_mul_inv_pow (hpat : IsConfluentPattern P t e)
    (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, 0 < e i → (P i).ord (t i) = 1)
    (hu : ∀ i j, u j ∈ (P i).toValuationSubring) (i₀ : Fin M) :
    (P i₀).evalAt (cofSec P t e u i₀ * (t i₀)⁻¹ ^ e i₀) = (jetMatrix P t e u).det := by
  rw [← Place.taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero (P i₀) (t i₀) _
      (taylorCoeff_cofSec_eq_zero_of_lt P t e u hpat hrat hord hu i₀),
    taylorCoeff_cofSec P t e u hrat hord hu i₀ i₀, if_pos rfl]

theorem ord_cofSec_self (hpat : IsConfluentPattern P t e)
    (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, 0 < e i → (P i).ord (t i) = 1)
    (hu : ∀ i j, u j ∈ (P i).toValuationSubring) (i₀ : Fin M)
    (hdet : (jetMatrix P t e u).det ≠ 0) :
    (P i₀).ord (cofSec P t e u i₀) = e i₀ := by
  have hU := cofSec_mem_toValuationSubring P t e u (P i₀) (hu i₀) i₀
  have hU0 := cofSec_ne_zero P t e u hrat hord hu i₀ hdet
  have htop := taylorCoeff_cofSec P t e u hrat hord hu i₀ i₀
  rw [if_pos rfl] at htop
  rcases Nat.eq_zero_or_pos (e i₀) with h0 | hpos
  ·
    rw [h0, Place.taylorCoeff_zero] at htop
    rw [h0]
    exact_mod_cast ord_eq_zero_of_evalAt_ne_zero (P i₀) (hrat i₀) hU0 hU (htop ▸ hdet)
  · have ht := hord i₀ hpos
    have h1 : ((e i₀ : ℕ) : ℤ) ≤ (P i₀).ord (cofSec P t e u i₀) :=
      (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord (P i₀) (hrat i₀) ht hU hU0 (e i₀)).mp
        (taylorCoeff_cofSec_eq_zero_of_lt P t e u hpat hrat hord hu i₀)
    have h2 : ¬ ((e i₀ + 1 : ℕ) : ℤ) ≤ (P i₀).ord (cofSec P t e u i₀) := by
      intro hle
      have h := (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord (P i₀) (hrat i₀) ht hU hU0
        (e i₀ + 1)).mpr hle (e i₀) (Nat.lt_succ_self _)
      exact hdet (htop ▸ h)
    push_cast at h2
    omega

theorem jetMult_le_ord_cofSec (hpat : IsConfluentPattern P t e)
    (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, 0 < e i → (P i).ord (t i) = 1)
    (hu : ∀ i j, u j ∈ (P i).toValuationSubring) (i₀ i : Fin M) (hne : P i ≠ P i₀)
    (hdet : (jetMatrix P t e u).det ≠ 0) :
    (jetMult P (P i) : ℤ) ≤ (P i).ord (cofSec P t e u i₀) := by
  have hU := cofSec_mem_toValuationSubring P t e u (P i) (hu i) i₀
  have hU0 := cofSec_ne_zero P t e u hrat hord hu i₀ hdet

  have hrow : ∀ q, q < jetMult P (P i) → (P i).taylorCoeff (t i) q (cofSec P t e u i₀) = 0 := by
    intro q hq
    obtain ⟨i', hP', he'⟩ := hpat.exists_eq_of_lt_jetMult i hq
    have hne' : i' ≠ i₀ := by rintro rfl; exact hne hP'.symm
    have h := taylorCoeff_cofSec P t e u hrat hord hu i₀ i'
    rw [if_neg hne', hP', hpat.1 i' i hP', he'] at h
    exact h
  by_cases hm : jetMult P (P i) ≤ 1
  ·
    have h1 : 1 ≤ jetMult P (P i) := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (hpat.2.2 i))
    have hm1 : jetMult P (P i) = 1 := le_antisymm hm h1
    have h0 := hrow 0 (by omega)
    rw [Place.taylorCoeff_zero] at h0
    rw [hm1]
    exact_mod_cast ord_pos_of_evalAt_eq_zero (P i) (hrat i) hU0 hU h0
  ·
    push_neg at hm
    obtain ⟨i', hP', he'⟩ := hpat.exists_eq_of_lt_jetMult i hm
    have ht : (P i).ord (t i) = 1 := by
      rw [← hpat.1 i' i hP', ← hP']; exact hord i' (by omega)
    exact (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord (P i) (hrat i) ht hU hU0 _).mp hrow

theorem le_ord_sum_of_forall (v : Place K F) {ι : Type*} (T : Finset ι) (g : ι → F) (n : ℤ)
    (hg : ∀ j ∈ T, g j = 0 ∨ n ≤ v.ord (g j)) (hne : ∑ j ∈ T, g j ≠ 0) :
    n ≤ v.ord (∑ j ∈ T, g j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp at hne
  | @insert j T hj ih =>
    rw [Finset.sum_insert hj] at hne ⊢
    have hgT : ∀ j' ∈ T, g j' = 0 ∨ n ≤ v.ord (g j') :=
      fun j' hj' => hg j' (Finset.mem_insert_of_mem hj')
    by_cases hS : ∑ j' ∈ T, g j' = 0
    · rw [hS, add_zero] at hne ⊢
      rcases hg j (Finset.mem_insert_self j T) with h | h
      · exact absurd h hne
      · exact h
    by_cases hgj : g j = 0
    · rw [hgj, zero_add] at hne ⊢
      exact ih hgT hS
    · rcases hg j (Finset.mem_insert_self j T) with h | h
      · exact absurd h hgj
      · exact le_trans (le_min h (ih hgT hS)) (Place.min_ord_le_ord_add v hgj hS hne)

theorem le_ord_cofSec_of_forall_le (v : Place K F) (i₀ : Fin M) (hU : cofSec P t e u i₀ ≠ 0)
    (hu0 : ∀ j, u j ≠ 0) (n : ℤ) (hn : ∀ j, n ≤ v.ord (u j)) : n ≤ v.ord (cofSec P t e u i₀) := by
  rw [cofSec_def] at hU ⊢
  refine le_ord_sum_of_forall v Finset.univ _ n (fun j _ => ?_) hU
  by_cases ha : (jetMatrix P t e u).adjugate j i₀ = 0
  · left; rw [ha, zero_smul]
  · right
    rw [Algebra.smul_def, Place.ord_mul v ((map_ne_zero _).mpr ha) (hu0 j), Place.ord_algebraMap,
      zero_add]
    exact hn j

end Generic

section Succ

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {n : ℕ} (P : Fin (n + 1) → Place K F) (t : Fin (n + 1) → F) (e : Fin (n + 1) → ℕ)
  (u : Fin (n + 1) → F)

theorem jetMatrix_submatrix {m : ℕ} (ρ σ : Fin m → Fin (n + 1)) :
    (jetMatrix P t e u).submatrix ρ σ = jetMatrix (P ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) := rfl

theorem jetMult_comp_succAbove_of_ne (i₀ : Fin (n + 1)) {v : Place K F} (h : P i₀ ≠ v) :
    jetMult (P ∘ i₀.succAbove) v = jetMult P v := by
  classical
  simp only [jetMult, Finset.card_filter, Fin.sum_univ_succAbove _ i₀, Function.comp_apply,
    if_neg h, zero_add]

theorem jetMult_comp_succAbove_self (i₀ : Fin (n + 1)) :
    jetMult (P ∘ i₀.succAbove) (P i₀) + 1 = jetMult P (P i₀) := by
  classical
  simp only [jetMult, Finset.card_filter, Fin.sum_univ_succAbove _ i₀, Function.comp_apply,
    ite_true]
  omega

theorem isConfluentPattern_comp_succAbove (hpat : IsConfluentPattern P t e) {i₀ : Fin (n + 1)}
    (htop : IsTopRow P e i₀) :
    IsConfluentPattern (P ∘ i₀.succAbove) (t ∘ i₀.succAbove) (e ∘ i₀.succAbove) := by
  refine ⟨fun a b h => hpat.1 _ _ h, fun a b hP he => Fin.succAbove_right_injective (hpat.2.1 _ _ hP he),
    fun a => ?_⟩
  have hlt := hpat.2.2 (i₀.succAbove a)
  simp only [Function.comp_apply]
  by_cases hP : P i₀ = P (i₀.succAbove a)
  · have hcount := jetMult_comp_succAbove_self P i₀
    rw [hP] at hcount
    have hne : e (i₀.succAbove a) ≠ e i₀ := fun he =>
      Fin.succAbove_ne i₀ a (hpat.2.1 _ _ hP.symm he)
    have hle : e (i₀.succAbove a) ≤ e i₀ := htop _ hP.symm
    have hlt0 := hpat.2.2 i₀
    rw [hP] at hlt0
    omega
  · rw [jetMult_comp_succAbove_of_ne P i₀ hP]
    exact hlt

theorem adjugate_jetMatrix_eq (i₀ j : Fin (n + 1)) :
    (jetMatrix P t e u).adjugate j i₀
      = (-1) ^ (i₀ + j : ℕ) * (jetMatrix (P ∘ i₀.succAbove) (t ∘ i₀.succAbove) (e ∘ i₀.succAbove)
          (u ∘ j.succAbove)).det :=
  Matrix.adjugate_fin_succ_eq_det_submatrix _ _ _

end Succ

end Alg

section Bookkeeping

variable {Pl : Type*} {M : ℕ}

open Classical in

noncomputable def ledgerRHS (R : Fin M → Pl) (MOV : Finset (Fin M)) (B : Pl →₀ ℤ)
    (ch : Fin M → ℝ) (pr : Pl → Pl → ℝ) (la : ℝ) (lfrow : Fin M → ℝ) {m : ℕ} (ρ : Fin m ↪ Fin M) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV), ch (ρ i)
    - (∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV),
        ∑ i' ∈ (Finset.univ.filter (fun i => ρ i ∈ MOV)).filter (fun i' => R (ρ i') ≠ R (ρ i)),
          pr (R (ρ i)) (R (ρ i'))) / 2
    - ∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV),
        ∑ i' ∈ Finset.univ.filter (fun i => ρ i ∉ MOV), pr (R (ρ i)) (R (ρ i'))
    - ∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV), B.sum (fun w n => (n : ℝ) * pr (R (ρ i)) w)
    + ((Finset.univ.filter (fun i => ρ i ∉ MOV)).card.factorial : ℝ) * la
    + ∑ i ∈ Finset.univ.filter (fun i => ρ i ∉ MOV), lfrow (ρ i)

theorem sum_filter_succAbove {β : Type*} [AddCommMonoid β] {n : ℕ} (p : Fin (n + 1) → Prop)
    [DecidablePred p] (f : Fin (n + 1) → β) (i₀ : Fin (n + 1)) :
    ∑ i ∈ Finset.univ.filter p, f i
      = (if p i₀ then f i₀ else 0) + ∑ a ∈ Finset.univ.filter (fun a => p (i₀.succAbove a)), f (i₀.succAbove a) := by
  rw [Finset.sum_filter, Fin.sum_univ_succAbove _ i₀, Finset.sum_filter]

theorem card_filter_succAbove {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] (i₀ : Fin (n + 1)) :
    (Finset.univ.filter p).card
      = (if p i₀ then 1 else 0) + (Finset.univ.filter (fun a => p (i₀.succAbove a))).card := by
  rw [Finset.card_filter, Fin.sum_univ_succAbove _ i₀, Finset.card_filter]

open Classical in

theorem ledgerRHS_succAbove (R : Fin M → Pl) (MOV : Finset (Fin M)) (B : Pl →₀ ℤ)
    (ch : Fin M → ℝ) (pr : Pl → Pl → ℝ) (hpr : ∀ v w, pr v w = pr w v) (la : ℝ) (lfrow : Fin M → ℝ)
    (hMOV : ∀ i i', R i = R i' → (i ∈ MOV ↔ i' ∈ MOV))
    {n : ℕ} (ρ : Fin (n + 1) ↪ Fin M) (i₀ : Fin (n + 1)) (hi₀ : ρ i₀ ∈ MOV) :
    ledgerRHS R MOV B ch pr la lfrow ρ
      = ledgerRHS R MOV B ch pr la lfrow ((Fin.succAboveEmb i₀).trans ρ) + ch (ρ i₀)
        - ∑ i ∈ Finset.univ.filter (fun i => R (ρ i) ≠ R (ρ i₀)), pr (R (ρ i₀)) (R (ρ i))
        - B.sum (fun w n => (n : ℝ) * pr (R (ρ i₀)) w) := by
  have hfixne : ∀ i, ρ i ∉ MOV → R (ρ i) ≠ R (ρ i₀) := fun i hi h => hi ((hMOV _ _ h).mpr hi₀)

  simp only [ledgerRHS, Function.Embedding.trans_apply, Fin.succAboveEmb_apply, Finset.filter_filter]

  simp only [sum_filter_succAbove _ _ i₀, card_filter_succAbove _ i₀]

  simp only [hi₀, not_true_eq_false, ne_eq, not_false_eq_true, and_true, and_false, true_and,
    ite_true, ite_false, zero_add, Finset.sum_add_distrib]

  have h1 : ∑ a ∈ Finset.univ.filter (fun a => ρ (i₀.succAbove a) ∈ MOV),
      (if ¬R (ρ i₀) = R (ρ (i₀.succAbove a)) then pr (R (ρ (i₀.succAbove a))) (R (ρ i₀)) else 0)
      = ∑ a ∈ Finset.univ.filter (fun a => ρ (i₀.succAbove a) ∈ MOV ∧ ¬R (ρ (i₀.succAbove a)) = R (ρ i₀)),
          pr (R (ρ i₀)) (R (ρ (i₀.succAbove a))) := by
    rw [← Finset.filter_filter, Finset.sum_filter (fun a => ¬R (ρ (i₀.succAbove a)) = R (ρ i₀))]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : R (ρ i₀) = R (ρ (i₀.succAbove a))
    · rw [if_neg (not_not_intro h), if_neg (not_not_intro h.symm)]
    · rw [if_pos h, if_pos (Ne.symm h), hpr]
  have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬R (ρ (i₀.succAbove a)) = R (ρ i₀)),
      pr (R (ρ i₀)) (R (ρ (i₀.succAbove a)))
      = ∑ a ∈ Finset.univ.filter (fun a => ρ (i₀.succAbove a) ∈ MOV ∧ ¬R (ρ (i₀.succAbove a)) = R (ρ i₀)),
          pr (R (ρ i₀)) (R (ρ (i₀.succAbove a)))
        + ∑ a ∈ Finset.univ.filter (fun a => ρ (i₀.succAbove a) ∉ MOV),
          pr (R (ρ i₀)) (R (ρ (i₀.succAbove a))) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun a => ρ (i₀.succAbove a) ∈ MOV),
      Finset.filter_filter, Finset.filter_filter]
    congr 1
    · exact Finset.sum_congr (Finset.filter_congr fun a _ => by tauto) fun _ _ => rfl
    · refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
      exact ⟨fun h => h.2, fun h => ⟨hfixne _ h, h⟩⟩
  rw [h1]
  rw [h2]
  ring

end Bookkeeping

section Local

open ModularCurve

def JLine (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (k : ℕ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (ν : ↥L → ℝ) (cν : ℝ) : Prop :=
  ∀ (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
    u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
    ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
    ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (v₀ = cuspInftyBar N ∨
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
    ∀ (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
    ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
    (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
    (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
    ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
    ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
    ∀ y : Fin r × Fin r → ↥L,
      (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
          = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
      (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
      Real.log (ν a)
        ≤ Real.log (⨆ φ, ν (c φ))
          + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
          + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
          - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
          + cν

theorem prox_comm {L : Type*} [CommRing L] {ι : Type*} (ν : AbsoluteValue L ℝ) (x y : ι → L) :
    prox ν x y = prox ν y x := by
  simp only [prox]
  have h : (fun p : ι × ι => ν (x p.1 * y p.2 - x p.2 * y p.1))
      = fun p : ι × ι => ν (y p.1 * x p.2 - y p.2 * x p.1) := by
    funext p; rw [← ν.map_neg]; congr 1; ring
  rw [h]; ring

end Local

namespace Glob

open ModularCurve NumberField

theorem pos_of_isEmbBasis (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) : 0 < r := by
  classical
  rcases Nat.eq_zero_or_pos r with h | h
  · exfalso
    subst h
    have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
      rw [mem_riemannRochSpace_iff]
      intro v
      right
      rw [Place.ord_one, neg_nonpos]
      simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul]
      refine mul_nonneg (by positivity) ?_
      rw [Finsupp.single_apply]
      split_ifs <;> norm_num
    rw [← hs.2, Set.range_eq_empty s, Submodule.span_empty, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

theorem abv_sum_le {L : Type*} [CommRing L] (ν : AbsoluteValue L ℝ) (Aν : ℝ) (hA1 : 1 ≤ Aν)
    (hA : ∀ a b : L, ν (a + b) ≤ Aν * max (ν a) (ν b)) {ι : Type*} (S : Finset ι) (f : ι → L)
    (b : ℝ) (hb : 0 ≤ b) (hf : ∀ i ∈ S, ν (f i) ≤ b) :
    ν (∑ i ∈ S, f i) ≤ Aν ^ S.card * b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hb]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
    have h1 : ν (f a) ≤ b := hf a (Finset.mem_insert_self _ _)
    have h2 : ν (∑ i ∈ S, f i) ≤ Aν ^ S.card * b := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hApow : 1 ≤ Aν ^ S.card := one_le_pow₀ hA1
    have hA0 : 0 ≤ Aν := by linarith
    calc ν (f a + ∑ i ∈ S, f i) ≤ Aν * max (ν (f a)) (ν (∑ i ∈ S, f i)) := hA _ _
      _ ≤ Aν * (Aν ^ S.card * b) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          refine max_le ?_ h2
          calc ν (f a) ≤ b := h1
            _ = 1 * b := (one_mul b).symm
            _ ≤ Aν ^ S.card * b := mul_le_mul_of_nonneg_right hApow hb
      _ = Aν ^ S.card * Aν * b := by ring

theorem infinitePlace_add_le {L : Type*} [Field L] (w : InfinitePlace L) (a b : L) :
    w.val (a + b) ≤ 2 * max (w.val a) (w.val b) := by
  calc w.val (a + b) ≤ w.val a + w.val b := w.val.add_le a b
    _ ≤ max (w.val a) (w.val b) + max (w.val a) (w.val b) := add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 2 * max (w.val a) (w.val b) := (two_mul _).symm

theorem finitePlace_add_le {L : Type*} [Field L] [NumberField L] (v : FinitePlace L) (a b : L) :
    v.val (a + b) ≤ 1 * max (v.val a) (v.val b) := by
  rw [one_mul]
  exact NumberField.FinitePlace.add_le v a b

theorem abv_det_le {L : Type*} [Field L] (ν : AbsoluteValue L ℝ) (Aν : ℝ) (hA1 : 1 ≤ Aν)
    (hA : ∀ a b : L, ν (a + b) ≤ Aν * max (ν a) (ν b)) {n : ℕ} (A : Matrix (Fin n) (Fin n) L)
    (b : Fin n → ℝ) (hb0 : ∀ i, 0 ≤ b i) (hb : ∀ i j, ν (A i j) ≤ b i) :
    ν A.det ≤ Aν ^ n.factorial * ∏ i, b i := by
  rw [Matrix.det_apply']
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← hcard]
  refine abv_sum_le ν Aν hA1 hA Finset.univ _ (∏ i, b i) (Finset.prod_nonneg fun i _ => hb0 i) ?_
  intro σ _
  rw [map_mul, AbsoluteValue.map_prod]
  have hsign : ν ((Equiv.Perm.sign σ : ℤ) : L) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, Units.val_one, Int.cast_one, map_one]
    · rw [h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, AbsoluteValue.map_neg, map_one]
  calc ν ((Equiv.Perm.sign σ : ℤ) : L) * ∏ i, ν (A (σ i) i) ≤ 1 * ∏ i, b (σ i) := by
        apply mul_le_mul hsign _ (Finset.prod_nonneg fun i _ => apply_nonneg _ _) zero_le_one
        exact Finset.prod_le_prod (fun i _ => apply_nonneg _ _) (fun i _ => hb (σ i) i)
    _ = ∏ i, b i := by rw [one_mul]; exact Equiv.prod_comp σ b

theorem log_abv_det_le {L : Type*} [Field L] (ν : AbsoluteValue L ℝ) (Aν : ℝ) (hA1 : 1 ≤ Aν)
    (hA : ∀ a b : L, ν (a + b) ≤ Aν * max (ν a) (ν b)) {n : ℕ} (A : Matrix (Fin n) (Fin n) L)
    (b : Fin n → ℝ) (hbpos : ∀ i, 0 < b i) (hb : ∀ i j, ν (A i j) ≤ b i) (hdet : A.det ≠ 0) :
    Real.log (ν A.det) ≤ (n.factorial : ℝ) * Real.log Aν + ∑ i, Real.log (b i) := by
  have h := abv_det_le ν Aν hA1 hA A b (fun i => (hbpos i).le) hb
  have hApos : 0 < Aν := by linarith
  have h1 := Real.log_le_log (ν.pos hdet) h
  rw [Real.log_mul (pow_ne_zero _ hApos.ne') (Finset.prod_pos fun i _ => hbpos i).ne', Real.log_pow,
    Real.log_prod (fun i _ => (hbpos i).ne')] at h1
  exact h1

end Glob

namespace Glob

open ModularCurve NumberField

theorem jline_arch (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hJarch : ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.InfinitePlace ↥L)
        (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (v₀ = cuspInftyBar N ∨
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
      ∀ (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (w : NumberField.InfinitePlace ↥L),
      JLine N s k L w (c₀ * k) := by
  obtain ⟨c₀, h⟩ := hJarch
  refine ⟨c₀, ?_⟩
  intro k L _ w
  unfold JLine
  intro c u hu0 hpres B hB v₀ hv₀ B' hB'0 hB'le x hxB' hxv₀ t ht a ha y hy hyne
  exact h k L c u hu0 hpres B hB w v₀ hv₀ B' hB'0 hB'le x hxB' hxv₀ t ht a ha y hy hyne

theorem jline_good (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hJgood : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (v : NumberField.FinitePlace ↥L),
        (∀ p ∈ S, v (p : ↥L) = 1) → JLine N s k L v 0 := by
  obtain ⟨S, hS, h⟩ := hJgood
  refine ⟨S, hS, ?_⟩
  intro k L _ v hv
  unfold JLine
  intro c u hu0 hpres B hB v₀ _hv₀ B' hB'0 hB'le x hxB' hxv₀ t ht a ha y hy hyne
  have := h k L c u hu0 hpres B hB v hv v₀ B' hB'0 hB'le x hxB' hxv₀ t ht a ha y hy hyne
  linarith

theorem jline_bad (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hJbad : ∀ S₀ : Finset ℕ, ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k * (-Real.log (ν (p : ↥L)))) :
    ∀ S₀ : Finset ℕ, ∃ c₀ : ℝ,
      ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (v : NumberField.FinitePlace ↥L) (p : ℕ),
        p.Prime → p ∈ S₀ → v (p : ↥L) < 1 → JLine N s k L v (c₀ * k * (-Real.log (v (p : ↥L)))) := by
  intro S₀
  obtain ⟨c₀, h⟩ := hJbad S₀
  refine ⟨c₀, ?_⟩
  intro k L _ v p hp hpS hv1
  unfold JLine
  intro c u hu0 hpres B hB v₀ _hv₀ B' hB'0 hB'le x hxB' hxv₀ t ht a ha y hy hyne
  exact h k L c u hu0 hpres B hB v p hp hpS hv1 v₀ B' hB'0 hB'le x hxB' hxv₀ t ht a ha y hy hyne

theorem peel_step (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (k : ℕ) {m : ℕ}
    (u' : Fin m → modularFunctionFieldBar N)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (ν : AbsoluteValue ↥L ℝ) (Aν cν : ℝ) (hA1 : 1 ≤ Aν)
    (hA : ∀ a b : ↥L, ν (a + b) ≤ Aν * max (ν a) (ν b))
    (hJ : JLine N s k L ν cν)
    (cfr : Fin m → (Fin k → Fin r) → ↥L)
    (hcfr : ∀ j, u' j = ∑ φ : Fin k → Fin r, ((cfr j φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l))
    (mL : Fin m → ↥L) (U : modularFunctionFieldBar N)
    (hU : U = ∑ j, ((mL j : ↥L) : AlgebraicClosure ℚ) • u' j) (hU0 : U ≠ 0)
    (BU : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hBU : ∀ w, BU w = w.ord U + ((k : ℤ) • embDivisor N) w)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (e₀ : ℕ) (hBUv : BU v₀ = e₀)
    (hv₀ : v₀ = cuspInftyBar N ∨
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ∈ v₀.toValuationSubring)
    (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB'0 : ∀ w, 0 ≤ B' w) (hB'le : ∀ w, B' w ≤ (BU.erase v₀) w)
    (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L)
    (hxB' : ∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i)
    (hxv₀ : ∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i)
    (t₀ : modularFunctionFieldBar N) (ht₀ : 0 < e₀ → v₀.ord t₀ = 1)
    (a : ↥L) (ha : (a : AlgebraicClosure ℚ) = regVal s v₀ t₀ k e₀ U)
    (y : Fin r × Fin r → ↥L)
    (hy : 0 < e₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ) = regVal s v₀ t₀ 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1))
    (hy0 : 0 < e₀ → y ≠ 0) :
    Real.log (ν a)
      ≤ Real.log (⨆ j : {j : Fin m // mL j ≠ 0}, ν (mL j.1))
        + Real.log (⨆ q : Fin m × (Fin k → Fin r), ν (cfr q.1 q.2))
        + (m : ℝ) * Real.log Aν
        + ((k : ℝ) - 2 * (e₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
        + (e₀ : ℝ) * Real.log (⨆ p, ν (y p))
        - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
        + cν := by
  classical

  have hmL : ∃ j, mL j ≠ 0 := by
    by_contra h
    push Not at h
    apply hU0
    rw [hU]
    exact Finset.sum_eq_zero fun j _ => by rw [h j, ZeroMemClass.coe_zero, zero_smul]
  haveI : Nonempty {j : Fin m // mL j ≠ 0} := let ⟨j, hj⟩ := hmL; ⟨⟨j, hj⟩⟩

  set cU : (Fin k → Fin r) → ↥L := fun φ => ∑ j, mL j * cfr j φ with hcU_def
  have hcoe : ∀ φ, ((cU φ : ↥L) : AlgebraicClosure ℚ) = ∑ j, ((mL j : ↥L) : AlgebraicClosure ℚ) * ((cfr j φ : ↥L) : AlgebraicClosure ℚ) := by
    intro φ
    simp [hcU_def]
  have hUpres : U = ∑ φ : Fin k → Fin r, ((cU φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) := by
    simp_rw [hcoe, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm, hU]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcfr j, Finset.smul_sum]
  have hcU : ∃ φ, cU φ ≠ 0 := by
    by_contra h
    push Not at h
    apply hU0
    rw [hUpres]
    exact Finset.sum_eq_zero fun φ _ => by rw [h φ, ZeroMemClass.coe_zero, zero_smul]
  haveI hne : Nonempty (Fin k → Fin r) := let ⟨φ, _⟩ := hcU; ⟨φ⟩
  have hcfr0 : ∃ q : Fin m × (Fin k → Fin r), cfr q.1 q.2 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨φ, hφ⟩ := hcU
    apply hφ
    simp only [hcU_def]
    exact Finset.sum_eq_zero fun j _ => by rw [h ⟨j, φ⟩, mul_zero]

  have ha' : (a : AlgebraicClosure ℚ) = regVal s v₀ t₀ k (BU v₀).toNat U := by
    rw [hBUv, Int.toNat_natCast]; exact ha
  have hpos : 0 < BU v₀ → 0 < e₀ := fun h => by rwa [hBUv, Int.natCast_pos] at h
  have hyne : 0 < BU v₀ → (⨆ p, ν (y p)) ≠ 0 := by
    intro h
    obtain ⟨p, hp⟩ : ∃ p, y p ≠ 0 := Function.ne_iff.mp (hy0 (hpos h))
    exact (Sum.iSup_pos_of_exists ν y ⟨p, ν.pos hp⟩).ne'
  have hline := hJ cU U hU0 hUpres BU hBU v₀ hv₀ B' hB'0 hB'le x hxB' hxv₀ t₀ (fun h => ht₀ (hpos h)) a ha' y
    (fun h => hy (hpos h)) hyne

  set Smc : ℝ := ⨆ j : {j : Fin m // mL j ≠ 0}, ν (mL j.1) with hSmc
  set Scf : ℝ := ⨆ q : Fin m × (Fin k → Fin r), ν (cfr q.1 q.2) with hScf
  set ScU : ℝ := ⨆ φ : Fin k → Fin r, ν (cU φ) with hScU
  have hSmc_pos : 0 < Smc := by
    obtain ⟨j, hj⟩ := hmL
    exact lt_of_lt_of_le (ν.pos hj) (Finite.le_ciSup_of_le (⟨j, hj⟩ : {j : Fin m // mL j ≠ 0}) le_rfl)
  have hScf_pos : 0 < Scf := by
    obtain ⟨q, hq⟩ := hcfr0
    exact lt_of_lt_of_le (ν.pos hq) (Finite.le_ciSup_of_le q le_rfl)
  have hScU_pos : 0 < ScU := by
    obtain ⟨φ, hφ⟩ := hcU
    exact lt_of_lt_of_le (ν.pos hφ) (Finite.le_ciSup_of_le φ le_rfl)
  have hSS : 0 ≤ Smc * Scf := (mul_pos hSmc_pos hScf_pos).le
  have hterm : ∀ j φ, ν (mL j * cfr j φ) ≤ Smc * Scf := by
    intro j φ
    rw [map_mul]
    rcases eq_or_ne (mL j) 0 with h0 | h0
    · rw [h0, map_zero, zero_mul]; exact hSS
    · exact mul_le_mul (Finite.le_ciSup_of_le (⟨j, h0⟩ : {j : Fin m // mL j ≠ 0}) le_rfl)
        (Finite.le_ciSup_of_le (⟨j, φ⟩ : Fin m × (Fin k → Fin r)) le_rfl) (apply_nonneg _ _) hSmc_pos.le
  have hcUφ : ∀ φ, ν (cU φ) ≤ Aν ^ m * (Smc * Scf) := by
    intro φ
    have h := abv_sum_le ν Aν hA1 hA Finset.univ (fun j => mL j * cfr j φ) (Smc * Scf) hSS
      (fun j _ => hterm j φ)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hScU_le : ScU ≤ Aν ^ m * (Smc * Scf) := ciSup_le hcUφ
  have hApos : 0 < Aν := by linarith
  have hlog : Real.log ScU ≤ (m : ℝ) * Real.log Aν + Real.log Smc + Real.log Scf := by
    have h1 : Real.log ScU ≤ Real.log (Aν ^ m * (Smc * Scf)) := Real.log_le_log hScU_pos hScU_le
    rw [Real.log_mul (pow_ne_zero _ hApos.ne') (mul_pos hSmc_pos hScf_pos).ne', Real.log_pow,
      Real.log_mul hSmc_pos.ne' hScf_pos.ne'] at h1
    linarith

  have hcast : ((BU v₀ : ℤ) : ℝ) = (e₀ : ℝ) := by rw [hBUv]; exact Int.cast_natCast e₀
  rw [hcast] at hline
  linarith [hline, hlog]

end Glob

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

section LevelN

open ModularCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] in
theorem evalAt_pow_of_mem (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (n : ℕ) : v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih]

variable {K F : Type*} [Field K] [Field F] [Algebra K F] in
theorem evalAt_inv_of_ord_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : v.ord f = 0) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.ge
  have hfi : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf0) (by rw [v.ord_inv, h, neg_zero])
  have hmul : v.evalAt f⁻¹ * v.evalAt f = 1 := by
    rw [← v.evalAt_mul_of_mem hv hfi hf, inv_mul_cancel₀ hf0, Place.evalAt_one]
  exact eq_inv_of_mul_eq_one_left hmul

variable (N : ℕ) [NeZero N]

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)

theorem embDivisor_apply_of_ne {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) : embDivisor N v = 0 := by
  classical
  simp [embDivisor, Finsupp.single_apply, Ne.symm hv]

theorem smul_embDivisor_apply_of_ne (k : ℕ) {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) : ((k : ℤ) • embDivisor N) v = 0 := by
  rw [Finsupp.smul_apply, embDivisor_apply_of_ne N hv, smul_zero]

theorem mem_toValuationSubring_of_mem_riemannRochSpace
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} {f : modularFunctionFieldBar N}
    (hf : f ∈ riemannRochSpace D) {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hD : D v = 0) : f ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  rcases (mem_riemannRochSpace_iff.mp hf) v with h0 | h
  · exact absurd h0 hf0
  · rw [hD, neg_zero] at h
    exact v.mem_toValuationSubring_of_ord_nonneg_alt hf0 h

theorem one_mem_riemannRochSpace_embDivisor :
    (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  classical
  rw [v.ord_one]
  simp only [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

variable {N}

theorem mem_riemannRochSpace_of_isEmbBasis {r : ℕ} {s : Fin r → modularFunctionFieldBar N}
    (hs : IsEmbBasis N s) (j : Fin r) : s j ∈ riemannRochSpace (embDivisor N) := by
  rw [← hs.2]; exact Submodule.subset_span ⟨j, rfl⟩

theorem ord_nonneg_of_isEmbBasis {r : ℕ} {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    (j : Fin r) {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hv : v ≠ cuspInftyBar N) :
    0 ≤ v.ord (s j) :=
  Alg.ord_nonneg_of_mem v (hs.1.ne_zero j)
    (mem_toValuationSubring_of_mem_riemannRochSpace N (mem_riemannRochSpace_of_isEmbBasis hs j)
      (embDivisor_apply_of_ne N hv))

theorem exists_ord_eq_zero_of_isEmbBasis {r : ℕ} {s : Fin r → modularFunctionFieldBar N}
    (hs : IsEmbBasis N s) {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) : ∃ j, v.ord (s j) = 0 := by
  by_contra h
  push_neg at h
  have hpos : ∀ j, (1 : ℤ) ≤ v.ord (s j) := fun j => by
    have h1 := ord_nonneg_of_isEmbBasis hs j hv
    have h2 := h j
    omega
  have h1mem : (1 : modularFunctionFieldBar N) ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
    rw [hs.2]; exact one_mem_riemannRochSpace_embDivisor N
  obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun (R := AlgebraicClosure ℚ).mp h1mem
  have hle : (1 : ℤ) ≤ v.ord (∑ j, a j • s j) := by
    refine Alg.le_ord_sum_of_forall v Finset.univ _ 1 (fun j _ => ?_) (by rw [ha]; exact one_ne_zero)
    by_cases haj : a j = 0
    · left; rw [haj, zero_smul]
    · right
      rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr haj) (hs.1.ne_zero j), v.ord_algebraMap,
        zero_add]
      exact hpos j
  rw [ha, v.ord_one] at hle
  omega

theorem ord_pivot_eq_zero {r : ℕ} (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hv : v ≠ cuspInftyBar N) :
    v.ord (s (pivotIndex s v hr)) = 0 := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i))
      ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  have hpiv : ∀ j, v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
    intro j
    unfold pivotIndex
    rw [dif_pos hex]
    exact Classical.choose_spec hex j
  obtain ⟨j, hj⟩ := exists_ord_eq_zero_of_isEmbBasis hs hv
  have h1 := hpiv j
  have h2 := ord_nonneg_of_isEmbBasis hs (pivotIndex s v hr) hv
  omega

end LevelN

section MainLocal
open ModularCurve

open Classical in

theorem local_ledger (N : ℕ) [NeZero N] {r : ℕ} (hr : 0 < r)
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k M : ℕ)
    (u : Fin M → modularFunctionFieldBar N) (hu0 : ∀ j, u j ≠ 0)
    (hu : ∀ j, u j ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, 0 ≤ B w)
    (hBu : ∀ j w, B w ≤ w.ord (u j) + ((k : ℤ) • embDivisor N) w)
    (R : Fin M → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : Fin M → modularFunctionFieldBar N) (e : Fin M → ℕ)
    (hpat : IsConfluentPattern R t e) (hR : ∀ i, R i ≠ cuspInftyBar N) (hRB : ∀ i, B (R i) = 0)
    (hRt : ∀ i, 0 < e i → (R i).ord (t i) = 1)
    (MOV : Finset (Fin M)) (hMOV : ∀ i i', R i = R i' → (i ∈ MOV ↔ i' ∈ MOV))
    (hadm : ∀ i ∈ MOV,
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ (R i).toValuationSubring)

    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : AbsoluteValue ↥L ℝ)
    (Aν : ℝ) (hA1 : 1 ≤ Aν) (hA : ∀ a b : ↥L, ν (a + b) ≤ Aν * max (ν a) (ν b))
    (cν : ℝ) (hJ : JLine N s k L ν cν)

    (cfr : Fin M → (Fin k → Fin r) → ↥L)
    (hcfr : ∀ j, u j = ∑ φ : Fin k → Fin r, ((cfr j φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l))
    (J : Matrix (Fin M) (Fin M) ↥L)
    (hJl : ∀ i j, ((J i j : ↥L) : AlgebraicClosure ℚ) = jetMatrix R t e u i j)
    (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L)
    (hx : ∀ w, (w ∈ B.support ∨ w ∈ Set.range R) → ∀ l, ((x w l : ↥L) : AlgebraicClosure ℚ) = evalVec s w l)
    (y : Fin M → Fin r × Fin r → ↥L)
    (hy : ∀ i, 0 < e i → ∀ p, ((y i p : ↥L) : AlgebraicClosure ℚ)
        = regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1))
    (hy0 : ∀ i, 0 < e i → y i ≠ 0)
    (π : Fin M → ↥L)
    (hπ : ∀ i, ((π i : ↥L) : AlgebraicClosure ℚ) = (R i).evalAt (s (pivotIndex s (R i) hr)))

    {m : ℕ} (ρ σ : Fin m ↪ Fin M) (hsub : IsConfluentPattern (R ∘ ρ) (t ∘ ρ) (e ∘ ρ))
    (hdet : (J.submatrix ρ σ).det ≠ 0) :
    Real.log (ν (J.submatrix ρ σ).det)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV),
          (Real.log (⨆ q : Fin M × (Fin k → Fin r), ν (cfr q.1 q.2)) + (M : ℝ) * Real.log Aν + cν
            + (k : ℝ) * Real.log (ν (π (ρ i)))
            + ((k : ℝ) - 2 * (e (ρ i) : ℝ)) * Real.log (⨆ l, ν (x (R (ρ i)) l))
            + (e (ρ i) : ℝ) * Real.log (⨆ p, ν (y (ρ i) p)))
        - (∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV),
            ∑ i' ∈ (Finset.univ.filter (fun i => ρ i ∈ MOV)).filter (fun i' => R (ρ i') ≠ R (ρ i)),
              prox ν (x (R (ρ i))) (x (R (ρ i')))) / 2
        - ∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV),
            ∑ i' ∈ Finset.univ.filter (fun i => ρ i ∉ MOV), prox ν (x (R (ρ i))) (x (R (ρ i')))
        - ∑ i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV),
            B.sum (fun w n => (n : ℝ) * prox ν (x (R (ρ i))) (x w))
        + ((Finset.univ.filter (fun i => ρ i ∉ MOV)).card.factorial : ℝ) * Real.log Aν
        + ∑ i ∈ Finset.univ.filter (fun i => ρ i ∉ MOV), Real.log (⨆ j : Fin M, ν (J (ρ i) j)) := by
  classical

  set Sc : ℝ := Real.log (⨆ q : Fin M × (Fin k → Fin r), ν (cfr q.1 q.2)) with hSc
  set ch : Fin M → ℝ := fun i => Sc + (M : ℝ) * Real.log Aν + cν + (k : ℝ) * Real.log (ν (π i))
      + ((k : ℝ) - 2 * (e i : ℝ)) * Real.log (⨆ l, ν (x (R i) l))
      + (e i : ℝ) * Real.log (⨆ p, ν (y i p)) with hch
  set pr : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ :=
    fun v w => prox ν (x v) (x w) with hpr
  set lf : Fin M → ℝ := fun i => Real.log (⨆ j, ν (J i j)) with hlf
  show Real.log (ν (J.submatrix ρ σ).det) ≤ ledgerRHS R MOV B ch pr (Real.log Aν) lf ρ

  have hcoe : ∀ z : ↥L, algebraMap ↥L (AlgebraicClosure ℚ) z = (z : AlgebraicClosure ℚ) := fun z => rfl
  have hlogA : 0 ≤ Real.log Aν := Real.log_nonneg hA1
  have hprsymm : ∀ v w, pr v w = pr w v := fun v w => prox_comm ν (x v) (x w)
  have hrat : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.IsRational := isRational_bar N
  have hureg : ∀ (i j : Fin M), u j ∈ (R i).toValuationSubring := fun i j =>
    mem_toValuationSubring_of_mem_riemannRochSpace N (hu j) (smul_embDivisor_apply_of_ne N k (hR i))
  have hΦne : Nonempty (Fin k → Fin r) := ⟨fun _ => ⟨0, hr⟩⟩

  suffices key : ∀ (n : ℕ) {m : ℕ} (ρ σ : Fin m ↪ Fin M),
      IsConfluentPattern (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) → (J.submatrix ρ σ).det ≠ 0 →
      (Finset.univ.filter (fun i => ρ i ∈ MOV)).card = n →
      Real.log (ν (J.submatrix ρ σ).det) ≤ ledgerRHS R MOV B ch pr (Real.log Aν) lf ρ from
    key _ ρ σ hsub hdet rfl
  intro n
  induction n with
  | zero =>
    intro m ρ σ hsubρ hdetρ hcard
    have hMOVe : Finset.univ.filter (fun i => ρ i ∈ MOV) = ∅ := Finset.card_eq_zero.mp hcard
    have hnone : ∀ i, ρ i ∉ MOV := by
      intro i hi
      have hmem : i ∈ Finset.univ.filter (fun i => ρ i ∈ MOV) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hMOVe] at hmem
      exact Finset.notMem_empty _ hmem
    have hFIX : Finset.univ.filter (fun i => ρ i ∉ MOV) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => hnone i
    simp only [ledgerRHS, hMOVe, hFIX, Finset.sum_empty, zero_div, sub_zero, zero_add, Finset.card_univ,
      Fintype.card_fin]
    have hb : ∀ i j, ν ((J.submatrix ρ σ) i j) ≤ ⨆ j', ν (J (ρ i) j') := fun i j =>
      le_ciSup (Finite.bddAbove_range fun j' => ν (J (ρ i) j')) (σ j)
    have hbpos : ∀ i, 0 < ⨆ j', ν (J (ρ i) j') := by
      intro i
      by_contra hle
      push_neg at hle
      apply hdetρ
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      have h2 : ν ((J.submatrix ρ σ) i j) ≤ 0 := (hb i j).trans hle
      exact ν.eq_zero.mp (le_antisymm h2 (ν.nonneg _))
    exact Glob.log_abv_det_le ν Aν hA1 hA (J.submatrix ρ σ) _ hbpos hb hdetρ
  | succ n ih =>
    intro m ρ σ hsubρ hdetρ hcard

    have hS : (Finset.univ.filter (fun i => ρ i ∈ MOV)).Nonempty := by
      rw [← Finset.card_pos, hcard]; exact Nat.succ_pos n
    obtain ⟨i₀, hi₀S, htop⟩ := Alg.exists_isTopRow (R ∘ ρ) (e ∘ ρ) _ hS (by
      intro i hi i' hP
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi hP ⊢
      exact (hMOV _ _ hP).mpr hi)
    have hi₀ : ρ i₀ ∈ MOV := (Finset.mem_filter.mp hi₀S).2

    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i₀)).symm⟩

    set J' : Matrix (Fin (m' + 1)) (Fin (m' + 1)) ↥L := J.submatrix ρ σ with hJ'
    have hrat' : ∀ i, ((R ∘ ρ) i).IsRational := fun i => hrat _
    have hord' : ∀ i, 0 < (e ∘ ρ) i → ((R ∘ ρ) i).ord ((t ∘ ρ) i) = 1 := fun i h => hRt (ρ i) h
    have hu'reg : ∀ i j, (u ∘ σ) j ∈ ((R ∘ ρ) i).toValuationSubring := fun i j => hureg (ρ i) (σ j)
    have hu'0 : ∀ j, (u ∘ σ) j ≠ 0 := fun j => hu0 (σ j)
    have hJ'map : J'.map (algebraMap ↥L (AlgebraicClosure ℚ)) = jetMatrix (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) := by
      ext i j
      simp only [Matrix.map_apply, hJ', Matrix.submatrix_apply, hcoe, hJl]
      rfl
    have hdetcoe : ((J'.det : ↥L) : AlgebraicClosure ℚ) = (jetMatrix (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ)).det := by
      rw [← hcoe, RingHom.map_det, RingHom.mapMatrix_apply, hJ'map]
    have hdet' : (jetMatrix (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ)).det ≠ 0 := by
      rw [← hdetcoe]; exact fun h => hdetρ (by exact_mod_cast h)

    set mL : Fin (m' + 1) → ↥L := fun j => J'.adjugate j i₀ with hmL
    set U : modularFunctionFieldBar N := Alg.cofSec (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) i₀ with hUdef
    have hmLcoe : ∀ j, ((mL j : ↥L) : AlgebraicClosure ℚ) = (jetMatrix (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ)).adjugate j i₀ := by
      intro j
      have h := RingHom.map_adjugate (algebraMap ↥L (AlgebraicClosure ℚ)) J'
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hJ'map] at h
      have hij := congrFun (congrFun h j) i₀
      rw [Matrix.map_apply] at hij
      rw [← hij]
      rfl
    have hU : U = ∑ j, ((mL j : ↥L) : AlgebraicClosure ℚ) • (u ∘ σ) j := by
      rw [hUdef, Alg.cofSec_def]
      exact Finset.sum_congr rfl fun j _ => by rw [hmLcoe]
    have hU0 : U ≠ 0 := Alg.cofSec_ne_zero (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) hrat' hord' hu'reg i₀ hdet'
    have hUreg : ∀ i, U ∈ (R (ρ i)).toValuationSubring := fun i =>
      Alg.cofSec_mem_toValuationSubring (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) (R (ρ i)) (hu'reg i) i₀

    haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
    obtain ⟨DU, hDU, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) U hU0
    set BU : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := DU + (k : ℤ) • embDivisor N with hBUdef
    have hBU : ∀ w, BU w = w.ord U + ((k : ℤ) • embDivisor N) w := fun w => by
      rw [hBUdef, Finsupp.add_apply, hDU w]

    have hv₀ne : (R (ρ i₀)) ≠ cuspInftyBar N := hR (ρ i₀)
    have hEv₀ : ((k : ℤ) • embDivisor N) (R (ρ i₀)) = 0 := smul_embDivisor_apply_of_ne N k hv₀ne
    have hordU : (R (ρ i₀)).ord U = (e (ρ i₀)) :=
      Alg.ord_cofSec_self (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) hsubρ hrat' hord' hu'reg i₀ hdet'
    have hBUv : BU (R (ρ i₀)) = (e (ρ i₀)) := by rw [hBU, hEv₀, add_zero, hordU]

    set B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      B + ∑ i ∈ Finset.univ.filter (fun i => R (ρ i) ≠ R (ρ i₀)), Finsupp.single (R (ρ i)) 1 with hB'def
    have hB'apply : ∀ w, B' w = B w
        + ((Finset.univ.filter (fun i => R (ρ i) ≠ R (ρ i₀) ∧ R (ρ i) = w)).card : ℤ) := by
      intro w
      rw [hB'def, Finsupp.add_apply, Finsupp.finset_sum_apply]
      congr 1
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : R (ρ i) = R (ρ i₀) <;> by_cases h2 : R (ρ i) = w <;> simp [h1, h2, Finsupp.single_apply]
    have hB'v₀ : B' (R (ρ i₀)) = 0 := by
      rw [hB'apply, hRB (ρ i₀)]
      simp
    have hB'of_ne : ∀ w, w ≠ (R (ρ i₀)) → B' w = B w + (jetMult (R ∘ ρ) w : ℤ) := by
      intro w hw
      rw [hB'apply]
      congr 2
      simp only [jetMult, Function.comp_apply]
      exact congrArg Finset.card (Finset.filter_congr fun i _ =>
        ⟨fun h => h.2, fun h => ⟨fun h' => hw (h.symm.trans h'), h⟩⟩)
    have hB'0 : ∀ w, 0 ≤ B' w := fun w => by
      rw [hB'apply]; exact add_nonneg (hB w) (Int.natCast_nonneg _)
    have hB'le : ∀ w, B' w ≤ (BU.erase (R (ρ i₀))) w := by
      intro w
      by_cases hw : w = (R (ρ i₀))
      · rw [hw, hB'v₀, Finsupp.erase_same]
      rw [Finsupp.erase_ne hw, hB'of_ne w hw, hBU]
      by_cases hrow : ∃ i, R (ρ i) = w
      · obtain ⟨i, rfl⟩ := hrow
        rw [hRB (ρ i), zero_add, smul_embDivisor_apply_of_ne N k (hR (ρ i)), add_zero]
        exact Alg.jetMult_le_ord_cofSec (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) hsubρ hrat' hord' hu'reg i₀ i hw hdet'
      · have hjm : jetMult (R ∘ ρ) w = 0 := by
          simp only [jetMult, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Function.comp_apply]
          exact fun i _ h => hrow ⟨i, h⟩
        rw [hjm, Nat.cast_zero, add_zero]
        have h : B w - ((k : ℤ) • embDivisor N) w ≤ w.ord U :=
          Alg.le_ord_cofSec_of_forall_le (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) w i₀ hU0 hu'0
            (B w - ((k : ℤ) • embDivisor N) w)
            (fun j => by show _ ≤ w.ord (u (σ j)); have := hBu (σ j) w; linarith)
        linarith

    have hB'supp : ∀ w ∈ B'.support, w ∈ B.support ∨ w ∈ Set.range R := by
      intro w hw
      rw [Finsupp.mem_support_iff, hB'apply] at hw
      by_cases hBw : B w = 0
      · right
        rw [hBw, zero_add, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos] at hw
        obtain ⟨i, hi⟩ := hw
        exact ⟨ρ i, (Finset.mem_filter.mp hi).2.2⟩
      · left; exact Finsupp.mem_support_iff.mpr hBw
    have hxB' : ∀ w ∈ B'.support, ∀ l, ((x w l : ↥L) : AlgebraicClosure ℚ) = evalVec s w l :=
      fun w hw l => hx w (hB'supp w hw) l
    have hxv₀ : ∀ l, ((x (R (ρ i₀)) l : ↥L) : AlgebraicClosure ℚ) = evalVec s (R (ρ i₀)) l :=
      fun l => hx (R (ρ i₀)) (Or.inr ⟨ρ i₀, rfl⟩) l

    have hv₀adm : (R (ρ i₀)) = cuspInftyBar N ∨
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ∈ (R (ρ i₀)).toValuationSubring := Or.inr (hadm (ρ i₀) hi₀)

    have hpiv0 : (R (ρ i₀)).ord (s (pivotIndex s (R (ρ i₀)) hr)) = 0 := ord_pivot_eq_zero hr hs hv₀ne
    have hpivne : (s (pivotIndex s (R (ρ i₀)) hr)) ≠ 0 := hs.1.ne_zero (pivotIndex s (R (ρ i₀)) hr)
    have hpivinvreg : (s (pivotIndex s (R (ρ i₀)) hr))⁻¹ ∈ (R (ρ i₀)).toValuationSubring :=
      (R (ρ i₀)).mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hpivne) (by rw [Place.ord_inv, hpiv0, neg_zero])
    have hevpiv : (R (ρ i₀)).evalAt (s (pivotIndex s (R (ρ i₀)) hr)) ≠ 0 := (R (ρ i₀)).evalAt_ne_zero_of_ord_eq_zero (hrat _) hpivne hpiv0
    have hπv₀ : ((π (ρ i₀) : ↥L) : AlgebraicClosure ℚ) = (R (ρ i₀)).evalAt (s (pivotIndex s (R (ρ i₀)) hr)) := hπ (ρ i₀)
    have hπne : π (ρ i₀) ≠ 0 := by
      intro h; apply hevpiv; rw [← hπv₀, h]; rfl

    have hUt_reg : U * (t (ρ i₀))⁻¹ ^ (e (ρ i₀)) ∈ (R (ρ i₀)).toValuationSubring := by
      rcases Nat.eq_zero_or_pos (e (ρ i₀)) with h0 | hpos
      · rw [h0, pow_zero, mul_one]; exact hUreg i₀
      · have ht1 : (R (ρ i₀)).ord (t (ρ i₀)) = 1 := hord' i₀ hpos
        have ht0 : (t (ρ i₀)) ≠ 0 := by
          intro h; rw [h, Place.ord_zero] at ht1; exact zero_ne_one ht1
        refine (R (ρ i₀)).mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hU0 (pow_ne_zero _ (inv_ne_zero ht0))) ?_
        rw [Place.ord_mul _ hU0 (pow_ne_zero _ (inv_ne_zero ht0)), hordU, ← zpow_natCast, Place.ord_zpow,
          Place.ord_inv, ht1]
        omega
    have hevUt : (R (ρ i₀)).evalAt (U * (t (ρ i₀))⁻¹ ^ (e (ρ i₀))) = (jetMatrix (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ)).det :=
      Alg.evalAt_cofSec_mul_inv_pow (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) (u ∘ σ) hsubρ hrat' hord' hu'reg i₀
    set a : ↥L := J'.det * (π (ρ i₀))⁻¹ ^ k with hadef
    have ha : (a : AlgebraicClosure ℚ) = regVal s (R (ρ i₀)) (t (ρ i₀)) k (e (ρ i₀)) U := by
      simp only [regVal, dif_pos hr]
      rw [show U * (s (pivotIndex s (R (ρ i₀)) hr))⁻¹ ^ k * (t (ρ i₀))⁻¹ ^ (e (ρ i₀)) = (U * (t (ρ i₀))⁻¹ ^ (e (ρ i₀))) * (s (pivotIndex s (R (ρ i₀)) hr))⁻¹ ^ k by ring,
        (R (ρ i₀)).evalAt_mul_of_mem (hrat _) hUt_reg (pow_mem hpivinvreg k), hevUt,
        evalAt_pow_of_mem (R (ρ i₀)) (hrat _) hpivinvreg, evalAt_inv_of_ord_eq_zero (R (ρ i₀)) (hrat _) hpivne hpiv0,
        hadef]
      push_cast
      rw [hdetcoe, hπv₀]

    have hy' : 0 < (e (ρ i₀)) → ∀ p, ((y (ρ i₀) p : ↥L) : AlgebraicClosure ℚ)
        = regVal s (R (ρ i₀)) (t (ρ i₀)) 1 1 (evalVec s (R (ρ i₀)) p.1 • s p.2 - evalVec s (R (ρ i₀)) p.2 • s p.1) :=
      fun h p => hy (ρ i₀) h p
    have hy0' : 0 < (e (ρ i₀)) → y (ρ i₀) ≠ 0 := fun h => hy0 (ρ i₀) h
    have hcfr' : ∀ j, (u ∘ σ) j = ∑ φ : Fin k → Fin r, ((cfr (σ j) φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) :=
      fun j => hcfr (σ j)

    have hstep := Glob.peel_step N s k (u ∘ σ) L ν Aν cν hA1 hA hJ (fun j => cfr (σ j)) hcfr' mL U hU hU0 BU hBU
      (R (ρ i₀)) (e (ρ i₀)) hBUv hv₀adm B' hB'0 hB'le x hxB' hxv₀ (t (ρ i₀)) (hord' i₀) a ha (y (ρ i₀)) hy' hy0'

    have hloga : Real.log (ν a) = Real.log (ν J'.det) - (k : ℝ) * Real.log (ν (π (ρ i₀))) := by
      rw [hadef, map_mul, map_pow, map_inv₀, Real.log_mul (ν.ne_zero hdetρ)
        (pow_ne_zero _ (inv_ne_zero (ν.ne_zero hπne))), Real.log_pow, Real.log_inv]
      ring

    have hcfr_sub : Real.log (⨆ q : Fin (m' + 1) × (Fin k → Fin r), ν (cfr (σ q.1) q.2)) ≤ Sc := by
      have hex : ∃ q : Fin (m' + 1) × (Fin k → Fin r), cfr (σ q.1) q.2 ≠ 0 := by
        by_contra h
        push_neg at h
        apply hu'0 0
        rw [hcfr' 0]
        exact Finset.sum_eq_zero fun φ _ => by rw [h (0, φ), ZeroMemClass.coe_zero, zero_smul]
      obtain ⟨q₀, hq₀⟩ := hex
      have hpos : 0 < ⨆ q : Fin (m' + 1) × (Fin k → Fin r), ν (cfr (σ q.1) q.2) :=
        lt_of_lt_of_le (ν.pos hq₀)
          (le_ciSup (Finite.bddAbove_range fun q : Fin (m' + 1) × (Fin k → Fin r) => ν (cfr (σ q.1) q.2)) q₀)
      refine Real.log_le_log hpos (ciSup_le fun q => ?_)
      exact le_ciSup (Finite.bddAbove_range fun q : Fin M × (Fin k → Fin r) => ν (cfr q.1 q.2)) (σ q.1, q.2)

    have hmM' : m' + 1 ≤ M := by simpa using Fintype.card_le_of_embedding ρ
    have hmM : ((m' + 1 : ℕ) : ℝ) * Real.log Aν ≤ (M : ℝ) * Real.log Aν :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmM') hlogA

    have hcof : Real.log (⨆ j : {j : Fin (m' + 1) // mL j ≠ 0}, ν (mL j.1))
        ≤ ledgerRHS R MOV B ch pr (Real.log Aν) lf ((Fin.succAboveEmb i₀).trans ρ) := by
      have hne : Nonempty {j : Fin (m' + 1) // mL j ≠ 0} := by
        by_contra h
        rw [not_nonempty_iff] at h
        apply hU0
        rw [hU]
        exact Finset.sum_eq_zero fun j _ => by
          have hj : mL j = 0 := by
            by_contra hj
            exact h.elim ⟨j, hj⟩
          rw [hj, ZeroMemClass.coe_zero, zero_smul]
      obtain ⟨⟨j₁, hj₁⟩, hjsup⟩ :=
        exists_eq_ciSup_of_finite (f := fun j : {j : Fin (m' + 1) // mL j ≠ 0} => ν (mL j.1))
      rw [← hjsup]
      set ρ₁ : Fin m' ↪ Fin M := (Fin.succAboveEmb i₀).trans ρ with hρ₁
      set σ₁ : Fin m' ↪ Fin M := (Fin.succAboveEmb j₁).trans σ with hσ₁
      have hminor : mL j₁ = (-1) ^ (i₀ + j₁ : ℕ) * (J.submatrix ρ₁ σ₁).det := by
        show J'.adjugate j₁ i₀ = _
        rw [hJ', Matrix.adjugate_fin_succ_eq_det_submatrix]
        rfl
      have hνmL : ν (mL j₁) = ν (J.submatrix ρ₁ σ₁).det := by
        rw [hminor, map_mul, map_pow, ν.map_neg, ν.map_one, one_pow, one_mul]
      have hdet₁ : (J.submatrix ρ₁ σ₁).det ≠ 0 := by
        intro h; apply hj₁; rw [hminor, h, mul_zero]
      have hsub₁ : IsConfluentPattern (R ∘ ρ₁) (t ∘ ρ₁) (e ∘ ρ₁) :=
        Alg.isConfluentPattern_comp_succAbove (R ∘ ρ) (t ∘ ρ) (e ∘ ρ) hsubρ htop
      have hcard₁ : (Finset.univ.filter (fun i => ρ₁ i ∈ MOV)).card = n := by
        have h := card_filter_succAbove (fun i => ρ i ∈ MOV) i₀
        rw [hcard, if_pos hi₀] at h
        have h' : (Finset.univ.filter (fun i => ρ₁ i ∈ MOV)).card
            = (Finset.univ.filter (fun a => ρ (i₀.succAbove a) ∈ MOV)).card :=
          congrArg Finset.card (Finset.filter_congr fun a _ => Iff.rfl)
        omega
      show Real.log (ν (mL j₁)) ≤ _
      rw [hνmL]
      exact ih ρ₁ σ₁ hsub₁ hdet₁ hcard₁

    have hB'sum : (B'.sum fun w n => (n : ℝ) * prox ν (x (R (ρ i₀))) (x w))
        = (B.sum fun w n => (n : ℝ) * prox ν (x (R (ρ i₀))) (x w))
          + ∑ i ∈ Finset.univ.filter (fun i => R (ρ i) ≠ R (ρ i₀)), prox ν (x (R (ρ i₀))) (x (R (ρ i))) := by
      rw [hB'def, Finsupp.sum_add_index']
      · congr 1
        rw [← Finsupp.sum_finset_sum_index]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finsupp.sum_single_index]
          · simp
          · simp
        · intro w; simp
        · intro w b₁ b₂; push_cast; ring
      · intro w; simp
      · intro w b₁ b₂; push_cast; ring

    rw [ledgerRHS_succAbove R MOV B ch pr hprsymm (Real.log Aν) lf hMOV ρ i₀ hi₀]
    have hch₀ : ch (ρ i₀) = Sc + (M : ℝ) * Real.log Aν + cν + (k : ℝ) * Real.log (ν (π (ρ i₀)))
        + ((k : ℝ) - 2 * ((e (ρ i₀)) : ℝ)) * Real.log (⨆ l, ν (x (R (ρ i₀)) l))
        + ((e (ρ i₀)) : ℝ) * Real.log (⨆ p, ν (y (ρ i₀) p)) := rfl
    rw [hch₀]
    rw [hloga, hB'sum] at hstep
    simp only [hpr] at hstep hcof ⊢
    linarith [hstep, hcof, hcfr_sub, hmM]

end MainLocal

namespace Glob

open ModularCurve NumberField

theorem sum_filter_lt {β : Type*} [AddCommMonoid β] (m m' : ℕ) (f : Fin (m + m') → β) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (m + m') => (i : ℕ) < m), f i = ∑ i : Fin m, f (Fin.castAdd m' i) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem sum_filter_not_lt {β : Type*} [AddCommMonoid β] (m m' : ℕ) (f : Fin (m + m') → β) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (m + m') => ¬ (i : ℕ) < m), f i = ∑ i' : Fin m', f (Fin.natAdd m i') := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem card_filter_not_lt (m m' : ℕ) :
    (Finset.univ.filter (fun i : Fin (m + m') => ¬ (i : ℕ) < m)).card = m' := by
  rw [Finset.card_eq_sum_ones, sum_filter_not_lt]
  simp

open Classical in

theorem top_local (N : ℕ) [NeZero N] {r : ℕ} (hr : 0 < r)
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k m m' : ℕ)
    (u : Fin (m + m') → modularFunctionFieldBar N) (hu0 : ∀ j, u j ≠ 0)
    (hu : ∀ j, u j ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, 0 ≤ B w)
    (hBu : ∀ j w, B w ≤ w.ord (u j) + ((k : ℤ) • embDivisor N) w)
    (R : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : Fin m → modularFunctionFieldBar N) (e : Fin m → ℕ)
    (R' : Fin m' → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t' : Fin m' → modularFunctionFieldBar N) (e' : Fin m' → ℕ)
    (hpat : IsConfluentPattern (Fin.append R R') (Fin.append t t') (Fin.append e e'))
    (hRR' : ∀ i i', R i ≠ R' i')
    (hR : ∀ i, R i ≠ cuspInftyBar N) (hR' : ∀ i', R' i' ≠ cuspInftyBar N)
    (hadm : ∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ∈ (R i).toValuationSubring)
    (hRB : ∀ i, B (R i) = 0) (hR'B : ∀ i', B (R' i') = 0)
    (hRt : ∀ i, 0 < e i → (R i).ord (t i) = 1) (hR't : ∀ i', 0 < e' i' → (R' i').ord (t' i') = 1)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : AbsoluteValue ↥L ℝ)
    (Aν : ℝ) (hA1 : 1 ≤ Aν) (hA : ∀ a b : ↥L, ν (a + b) ≤ Aν * max (ν a) (ν b))
    (cν : ℝ) (hJ : JLine N s k L ν cν)
    (cfr : Fin (m + m') → (Fin k → Fin r) → ↥L)
    (hcfr : ∀ j, u j = ∑ φ : Fin k → Fin r, ((cfr j φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l))
    (J : Matrix (Fin (m + m')) (Fin (m + m')) ↥L)
    (hJl : ∀ i j, ((J i j : ↥L) : AlgebraicClosure ℚ) = jetMatrix (Fin.append R R') (Fin.append t t') (Fin.append e e') u i j)
    (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L)
    (hx : ∀ w, (w ∈ B.support ∨ w ∈ Set.range (Fin.append R R')) → ∀ l, ((x w l : ↥L) : AlgebraicClosure ℚ) = evalVec s w l)
    (y : Fin (m + m') → Fin r × Fin r → ↥L)
    (hy : ∀ i, 0 < Fin.append e e' i → ∀ p, ((y i p : ↥L) : AlgebraicClosure ℚ)
        = regVal s (Fin.append R R' i) (Fin.append t t' i) 1 1
            (evalVec s (Fin.append R R' i) p.1 • s p.2 - evalVec s (Fin.append R R' i) p.2 • s p.1))
    (hy0 : ∀ i, 0 < Fin.append e e' i → y i ≠ 0)
    (π : Fin (m + m') → ↥L)
    (hπ : ∀ i, ((π i : ↥L) : AlgebraicClosure ℚ) = (Fin.append R R' i).evalAt (s (pivotIndex s (Fin.append R R' i) hr)))
    (hdet : J.det ≠ 0) :
    Real.log (ν J.det)
      ≤ ∑ i : Fin m,
          (Real.log (⨆ q : Fin (m + m') × (Fin k → Fin r), ν (cfr q.1 q.2)) + ((m + m' : ℕ) : ℝ) * Real.log Aν + cν
            + (k : ℝ) * Real.log (ν (π (Fin.castAdd m' i)))
            + ((k : ℝ) - 2 * (e i : ℝ)) * Real.log (⨆ l, ν (x (R i) l))
            + (e i : ℝ) * Real.log (⨆ p, ν (y (Fin.castAdd m' i) p)))
        - (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i),
              prox ν (x (R i)) (x (R i'))) / 2
        - ∑ i : Fin m, ∑ i' : Fin m', prox ν (x (R i)) (x (R' i'))
        - ∑ i : Fin m, B.sum (fun w n => (n : ℝ) * prox ν (x (R i)) (x w))
        + ((m'.factorial : ℕ) : ℝ) * Real.log Aν
        + ∑ i' : Fin m', Real.log (⨆ j : Fin (m + m'), ν (J (Fin.natAdd m i') j)) := by
  classical

  set MOV : Finset (Fin (m + m')) := Finset.univ.filter (fun i : Fin (m + m') => (i : ℕ) < m) with hMOV_def
  have hmemMOV : ∀ i : Fin (m + m'), i ∈ MOV ↔ (i : ℕ) < m := fun i => by simp [hMOV_def]
  have hcast_mem : ∀ i : Fin m, Fin.castAdd m' i ∈ MOV := fun i => (hmemMOV _).mpr (by simp)
  have hnat_nmem : ∀ i' : Fin m', Fin.natAdd m i' ∉ MOV := fun i' => by
    rw [hmemMOV]; simp
  have hRall : ∀ i, Fin.append R R' i ≠ cuspInftyBar N := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i' => ?_) i
    · rw [Fin.append_left]; exact hR i
    · rw [Fin.append_right]; exact hR' i'
  have hRBall : ∀ i, B (Fin.append R R' i) = 0 := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i' => ?_) i
    · rw [Fin.append_left]; exact hRB i
    · rw [Fin.append_right]; exact hR'B i'
  have hRtall : ∀ i, 0 < Fin.append e e' i → (Fin.append R R' i).ord (Fin.append t t' i) = 1 := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i' => ?_) i
    · simp only [Fin.append_left]; exact hRt i
    · simp only [Fin.append_right]; exact hR't i'
  have hMOV : ∀ i i', Fin.append R R' i = Fin.append R R' i' → (i ∈ MOV ↔ i' ∈ MOV) := by
    intro i i'
    refine Fin.addCases (fun i₀ => ?_) (fun i₀' => ?_) i <;>
      refine Fin.addCases (fun j₀ => ?_) (fun j₀' => ?_) i' <;> intro h
    · exact ⟨fun _ => hcast_mem _, fun _ => hcast_mem _⟩
    · rw [Fin.append_left, Fin.append_right] at h; exact absurd h (hRR' i₀ j₀')
    · rw [Fin.append_right, Fin.append_left] at h; exact absurd h.symm (hRR' j₀ i₀')
    · exact ⟨fun h' => absurd h' (hnat_nmem _), fun h' => absurd h' (hnat_nmem _)⟩
  have hadmall : ∀ i ∈ MOV, (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
      modularFunctionFieldBar N) ∈ (Fin.append R R' i).toValuationSubring := by
    intro i hi
    induction i using Fin.addCases with
    | left i₀ => rw [Fin.append_left]; exact hadm i₀
    | right i₀' => exact absurd hi (hnat_nmem _)
  have hsubJ : J.submatrix (Function.Embedding.refl (Fin (m + m'))) (Function.Embedding.refl (Fin (m + m'))) = J :=
    Matrix.ext fun _ _ => rfl
  have hdet' : (J.submatrix (Function.Embedding.refl (Fin (m + m'))) (Function.Embedding.refl (Fin (m + m')))).det ≠ 0 := by
    rw [hsubJ]; exact hdet
  have h := local_ledger N hr s hs k (m + m') u hu0 hu B hB hBu (Fin.append R R') (Fin.append t t') (Fin.append e e')
    hpat hRall hRBall hRtall MOV hMOV hadmall L ν Aν hA1 hA cν hJ cfr hcfr J hJl x hx y hy hy0 π hπ
    (Function.Embedding.refl _) (Function.Embedding.refl _) hpat hdet'
  rw [hsubJ] at h
  simp only [Function.Embedding.refl_apply] at h

  have hfilt : Finset.univ.filter (fun i : Fin (m + m') => i ∈ MOV) = MOV := by
    ext i; simp
  have hfilt' : Finset.univ.filter (fun i : Fin (m + m') => i ∉ MOV)
      = Finset.univ.filter (fun i : Fin (m + m') => ¬ (i : ℕ) < m) := by
    ext i; simp [hmemMOV]
  rw [hfilt, hfilt'] at h
  rw [card_filter_not_lt] at h
  simp only [sum_filter_not_lt] at h
  simp only [Finset.sum_filter] at h
  simp only [hMOV_def, sum_filter_lt, Fin.append_left, Fin.append_right] at h
  simp only [Finset.sum_filter]
  linarith [h]

end Glob

end ConfLedger

end

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

open Classical in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k m m' : ℕ)

    (hJgood : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w)))
    (hJbad : ∀ S₀ : Finset ℕ, ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k * (-Real.log (ν (p : ↥L))))
    (hJarch : ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.InfinitePlace ↥L)
        (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (v₀ = cuspInftyBar N ∨
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
      ∀ (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k)
    (H : ℝ) :
    ∃ C : ℝ, ∀ (u : Fin (m + m') → modularFunctionFieldBar N)
      (c : Fin (m + m') → (Fin k → Fin r) → AlgebraicClosure ℚ),
      (∀ j, u j ≠ 0) → (∀ j, u j = ∑ φ : Fin k → Fin r, c j φ • ∏ l, s (φ l)) →
      absLogHeight (fun q : Fin (m + m') × (Fin k → Fin r) => c q.1 q.2) ≤ H →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, 0 ≤ B w) →
      (∀ j w, B w ≤ w.ord (u j) + ((k : ℤ) • embDivisor N) w) →
      ∀ (R : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : Fin m → modularFunctionFieldBar N) (e : Fin m → ℕ)
        (R' : Fin m' → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t' : Fin m' → modularFunctionFieldBar N) (e' : Fin m' → ℕ),
      IsConfluentPattern (Fin.append R R') (Fin.append t t') (Fin.append e e') →
      (∀ i i', R i ≠ R' i') →
      (∀ i, R i ≠ cuspInftyBar N) → (∀ i', R' i' ≠ cuspInftyBar N) →
      (∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ∈ (R i).toValuationSubring) →
      (∀ i, B (R i) = 0) → (∀ i', B (R' i') = 0) →
      (∀ i, 0 < e i → (R i).ord (t i) = 1) → (∀ i', 0 < e' i' → (R' i').ord (t' i') = 1) →
      IsUnit (jetMatrix (Fin.append R R') (Fin.append t t') (Fin.append e e') u).det →
      (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i')) / 2
        + ∑ i : Fin m, ∑ i' : Fin m', pairHt s (R i) (R' i')
        + ∑ i : Fin m, B.sum (fun w n => (n : ℝ) * pairHt s (R i) w)
        ≤ ∑ i : Fin m,
            (((k : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
              + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                  regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1)))
          + ∑ i' : Fin m', absLogHeight (fun j : Fin (m + m') => (R' i').taylorCoeff (t' i') (e' i') (u j))
          + C := by
  classical

  obtain ⟨S, hSprime, hJg⟩ := ConfLedger.Glob.jline_good N s hJgood
  obtain ⟨cA, hJa⟩ := ConfLedger.Glob.jline_arch N s hJarch
  obtain ⟨cB, hJb⟩ := ConfLedger.Glob.jline_bad N s hJbad S
  refine ⟨(m : ℝ) * (H + ((m + m') : ℕ) * Real.log 2 + |cA| * k + |cB| * k * ∑ p ∈ S, Real.log p)
      + ((m'.factorial : ℕ) : ℝ) * Real.log 2, ?_⟩
  intro u c hu0 hc hH B hB hBu R t e R' t' e' hpat hRR' hR hR' hadm hRB hR'B hRt hR't hunit
  have hr : 0 < r := ConfLedger.Glob.pos_of_isEmbBasis N s hs
  have hu : ∀ j, u j ∈ riemannRochSpace ((k : ℤ) • embDivisor N) := fun j =>
    mem_riemannRochSpace_iff.mpr fun v => Or.inr (by have h1 := hBu j v; have h2 := hB v; linarith)

  set Ra : Fin (m + m') → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := Fin.append R R' with hRa
  set ta : Fin (m + m') → modularFunctionFieldBar N := Fin.append t t' with hta
  set ea : Fin (m + m') → ℕ := Fin.append e e' with hea
  have hRta : ∀ i, 0 < ea i → (Ra i).ord (ta i) = 1 := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i' => ?_) i
    · simp only [hRa, hta, hea, Fin.append_left]; exact hRt i
    · simp only [hRa, hta, hea, Fin.append_right]; exact hR't i'

  set P : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := B.support ∪ Finset.univ.image Ra with hP
  have hPB : ∀ w ∈ B.support, w ∈ P := fun w hw => Finset.mem_union_left _ hw
  have hPR : ∀ i, Ra i ∈ P := fun i =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hPRl : ∀ i, R i ∈ P := fun i => by
    have := hPR (Fin.castAdd m' i); simp only [hRa, Fin.append_left] at this; exact this
  have hPRr : ∀ i', R' i' ∈ P := fun i' => by
    have := hPR (Fin.natAdd m i'); simp only [hRa, Fin.append_right] at this; exact this

  set Ytan : Fin (m + m') → Fin r × Fin r → AlgebraicClosure ℚ := fun i p =>
    regVal s (Ra i) (ta i) 1 1 (evalVec s (Ra i) p.1 • s p.2 - evalVec s (Ra i) p.2 • s p.1) with hYtan
  set Jq : Matrix (Fin (m + m')) (Fin (m + m')) (AlgebraicClosure ℚ) := jetMatrix Ra ta ea u with hJq
  set πq : Fin (m + m') → AlgebraicClosure ℚ := fun i => (Ra i).evalAt (s (pivotIndex s (Ra i) hr)) with hπq
  let big : ((↥P × Fin r) ⊕ ((Fin (m + m') × (Fin r × Fin r)) ⊕ ((Fin (m + m') × (Fin k → Fin r))
      ⊕ ((Fin (m + m') × Fin (m + m')) ⊕ Fin (m + m'))))) → AlgebraicClosure ℚ :=
    fun z => Sum.elim (fun wi => evalVec s (wi.1 : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) wi.2)
      (Sum.elim (fun ip => Ytan ip.1 ip.2)
        (Sum.elim (fun q => c q.1 q.2)
          (Sum.elim (fun ij => Jq ij.1 ij.2) (fun i => πq i)))) z
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ (Set.range big) with hL
  haveI hLfd : FiniteDimensional ℚ ↥L := finiteDimensional_adjoin_range big
  have memL : ∀ z, big z ∈ L := fun z => IntermediateField.subset_adjoin ℚ _ ⟨z, rfl⟩

  set x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L := fun w l =>
    if h : w ∈ P then ⟨evalVec s w l, memL (Sum.inl (⟨w, h⟩, l))⟩ else 0 with hx_def
  have hxP : ∀ w ∈ P, ∀ l, ((x w l : ↥L) : AlgebraicClosure ℚ) = evalVec s w l := by
    intro w hw l
    have : x w l = ⟨evalVec s w l, memL (Sum.inl (⟨w, hw⟩, l))⟩ := dif_pos hw
    rw [this]
  have hx : ∀ w, (w ∈ B.support ∨ w ∈ Set.range Ra) → ∀ l, ((x w l : ↥L) : AlgebraicClosure ℚ) = evalVec s w l := by
    rintro w (hw | ⟨i, rfl⟩) l
    · exact hxP w (hPB w hw) l
    · exact hxP _ (hPR i) l
  let y : Fin (m + m') → Fin r × Fin r → ↥L := fun i p => ⟨Ytan i p, memL (Sum.inr (Sum.inl (i, p)))⟩
  have hyv : ∀ i p, ((y i p : ↥L) : AlgebraicClosure ℚ) = Ytan i p := fun i p => rfl
  have hy : ∀ i, 0 < ea i → ∀ p, ((y i p : ↥L) : AlgebraicClosure ℚ)
      = regVal s (Ra i) (ta i) 1 1 (evalVec s (Ra i) p.1 • s p.2 - evalVec s (Ra i) p.2 • s p.1) :=
    fun i _ p => rfl
  have hy0 : ∀ i, 0 < ea i → y i ≠ 0 := by
    intro i hi h0
    obtain ⟨p, hp⟩ := ModularCurve.JZero.exists_regVal_chord_ne_zero N s hs (Ra i) (ta i) (hRta i hi)
    exact hp (congrArg Subtype.val (congrFun h0 p))
  let cfr : Fin (m + m') → (Fin k → Fin r) → ↥L := fun j φ => ⟨c j φ, memL (Sum.inr (Sum.inr (Sum.inl (j, φ))))⟩
  have hcfrv : ∀ j φ, ((cfr j φ : ↥L) : AlgebraicClosure ℚ) = c j φ := fun j φ => rfl
  have hcfr : ∀ j, u j = ∑ φ : Fin k → Fin r, ((cfr j φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) := fun j => hc j
  let J : Matrix (Fin (m + m')) (Fin (m + m')) ↥L :=
    Matrix.of fun i j => ⟨Jq i j, memL (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))⟩
  have hJl : ∀ i j, ((J i j : ↥L) : AlgebraicClosure ℚ) = jetMatrix Ra ta ea u i j := fun i j => rfl
  let π : Fin (m + m') → ↥L := fun i => ⟨πq i, memL (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))⟩
  have hπ : ∀ i, ((π i : ↥L) : AlgebraicClosure ℚ) = (Ra i).evalAt (s (pivotIndex s (Ra i) hr)) := fun i => rfl

  have hdetq : (jetMatrix Ra ta ea u).det ≠ 0 := hunit.ne_zero
  have hJmap : (L.val.toRingHom).mapMatrix J = jetMatrix Ra ta ea u := by
    ext i j; rfl
  have hdetL : (((J.det : ↥L)) : AlgebraicClosure ℚ) = (jetMatrix Ra ta ea u).det := by
    have h1 := RingHom.map_det L.val.toRingHom J
    rw [hJmap] at h1
    exact h1
  have hdet : J.det ≠ 0 := by
    intro h0; apply hdetq; rw [← hdetL, h0]; rfl

  let mn : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r × Fin r → ↥L := fun o w q => x o q.1 * x w q.2 - x o q.2 * x w q.1
  let cvec : Fin (m + m') × (Fin k → Fin r) → ↥L := fun q => cfr q.1 q.2
  set T : Finset (NumberField.FinitePlace ↥L) :=
    P.biUnion (fun w => ConfLedger.Sum.vsupp (x w))
      ∪ (P ×ˢ P).biUnion (fun ow => ConfLedger.Sum.vsupp (mn ow.1 ow.2))
      ∪ Finset.univ.biUnion (fun i => ConfLedger.Sum.vsupp (y i))
      ∪ ConfLedger.Sum.vsupp cvec
      ∪ Finset.univ.biUnion (fun i => ConfLedger.Sum.vsupp (fun j => J i j))
      ∪ ConfLedger.Sum.csupp J.det
      ∪ Finset.univ.biUnion (fun i => ConfLedger.Sum.csupp (π i))
      ∪ S.biUnion (fun p => ConfLedger.Sum.csupp (p : ↥L)) with hT
  have hTx : ∀ w ∈ P, x w ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => ⨆ i, v (x w i)) ⊆ ↑T := by
    intro w hw hne v hv
    have h1 : v ∈ P.biUnion (fun w => ConfLedger.Sum.vsupp (x w)) :=
      Finset.mem_biUnion.mpr ⟨w, hw, ConfLedger.Sum.vsupp_spec (x w) hne hv⟩
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTmn : ∀ o ∈ P, ∀ w ∈ P, mn o w ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => ⨆ q, v (mn o w q)) ⊆ ↑T := by
    intro o ho w hw hne v hv
    have h1 : v ∈ (P ×ˢ P).biUnion (fun ow => ConfLedger.Sum.vsupp (mn ow.1 ow.2)) :=
      Finset.mem_biUnion.mpr ⟨(o, w), Finset.mem_product.mpr ⟨ho, hw⟩, ConfLedger.Sum.vsupp_spec (mn o w) hne hv⟩
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTy : ∀ i, y i ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => ⨆ q, v (y i q)) ⊆ ↑T := by
    intro i hne v hv
    have h1 : v ∈ Finset.univ.biUnion (fun i => ConfLedger.Sum.vsupp (y i)) :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ConfLedger.Sum.vsupp_spec (y i) hne hv⟩
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTc : cvec ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => ⨆ q, v (cvec q)) ⊆ ↑T := by
    intro hne v hv
    have h1 : v ∈ ConfLedger.Sum.vsupp cvec := ConfLedger.Sum.vsupp_spec cvec hne hv
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTJ : ∀ i, (fun j => J i j) ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => ⨆ j, v (J i j)) ⊆ ↑T := by
    intro i hne v hv
    have h1 : v ∈ Finset.univ.biUnion (fun i => ConfLedger.Sum.vsupp (fun j => J i j)) :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ConfLedger.Sum.vsupp_spec (fun j => J i j) hne hv⟩
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTdet : J.det ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => v J.det) ⊆ ↑T := by
    intro hne v hv
    have h1 : v ∈ ConfLedger.Sum.csupp J.det := ConfLedger.Sum.csupp_spec J.det hne hv
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTπ : ∀ i, π i ≠ 0 →
      Function.mulSupport (fun v : NumberField.FinitePlace ↥L => v (π i)) ⊆ ↑T := by
    intro i hne v hv
    have h1 : v ∈ Finset.univ.biUnion (fun i => ConfLedger.Sum.csupp (π i)) :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ConfLedger.Sum.csupp_spec (π i) hne hv⟩
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]
  have hTp : ∀ p ∈ S, Function.mulSupport (fun v : NumberField.FinitePlace ↥L => v (p : ↥L)) ⊆ ↑T := by
    intro p hp v hv
    have hp0 : (p : ↥L) ≠ 0 := Nat.cast_ne_zero.mpr (hSprime p hp).ne_zero
    have h1 : v ∈ S.biUnion (fun p => ConfLedger.Sum.csupp (p : ↥L)) :=
      Finset.mem_biUnion.mpr ⟨p, hp, ConfLedger.Sum.csupp_spec (p : ↥L) hp0 hv⟩
    rw [Finset.mem_coe, hT]; simp only [Finset.mem_union, h1, true_or, or_true]

  let Lp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → (↥L → ℝ) → ℝ := fun o w =>
    ConfLedger.Sum.La (x o) + ConfLedger.Sum.La (x w) - ConfLedger.Sum.La (mn o w)
  have hLp : ∀ o w (ν : ↥L → ℝ), Lp o w ν = prox ν (x o) (x w) := fun o w ν => rfl
  set Ψ : (↥L → ℝ) → ℝ :=
    ((1 / 2 : ℝ) • ∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), Lp (R i) (R i'))
    + (∑ i : Fin m, ∑ i' : Fin m', Lp (R i) (R' i'))
    + (∑ i : Fin m, ∑ w ∈ B.support, ((B w : ℤ) : ℝ) • Lp (R i) w)
    - (∑ i : Fin m, ((((k : ℝ) - 2 * (e i : ℝ)) • ConfLedger.Sum.La (x (R i)))
        + (e i : ℝ) • ConfLedger.Sum.La (y (Fin.castAdd m' i))))
    + ConfLedger.Sum.Lc J.det - (m : ℝ) • ConfLedger.Sum.La cvec
    - (k : ℝ) • (∑ i : Fin m, ConfLedger.Sum.Lc (π (Fin.castAdd m' i)))
    - (∑ i' : Fin m', ConfLedger.Sum.La (fun j => J (Fin.natAdd m i') j)) with hΨ
  have eΨ : ∀ ν : ↥L → ℝ, Ψ ν
      = (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), prox ν (x (R i)) (x (R i'))) / 2
        + (∑ i : Fin m, ∑ i' : Fin m', prox ν (x (R i)) (x (R' i')))
        + (∑ i : Fin m, B.sum (fun w n => (n : ℝ) * prox ν (x (R i)) (x w)))
        - (∑ i : Fin m, (((k : ℝ) - 2 * (e i : ℝ)) * Real.log (⨆ l, ν (x (R i) l))
            + (e i : ℝ) * Real.log (⨆ p, ν (y (Fin.castAdd m' i) p))))
        + Real.log (ν J.det) - (m : ℝ) * Real.log (⨆ q : Fin (m + m') × (Fin k → Fin r), ν (cfr q.1 q.2))
        - (k : ℝ) * (∑ i : Fin m, Real.log (ν (π (Fin.castAdd m' i))))
        - (∑ i' : Fin m', Real.log (⨆ j : Fin (m + m'), ν (J (Fin.natAdd m i') j))) := by
    intro ν
    simp only [hΨ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hLp,
      ConfLedger.Sum.La_apply, ConfLedger.Sum.Lc_apply, Finsupp.sum]
    ring

  have perplace : ∀ (ν : AbsoluteValue ↥L ℝ) (Aν : ℝ), 1 ≤ Aν → (∀ a b : ↥L, ν (a + b) ≤ Aν * max (ν a) (ν b)) →
      ∀ cν : ℝ, ConfLedger.JLine N s k L ν cν →
        Ψ ν ≤ (m : ℝ) * ((m + m') : ℕ) * Real.log Aν + (m : ℝ) * cν + ((m'.factorial : ℕ) : ℝ) * Real.log Aν := by
    intro ν Aν hA1 hA cν hJ
    have h := ConfLedger.Glob.top_local N hr s hs k m m' u hu0 hu B hB hBu R t e R' t' e' hpat hRR' hR hR'
      hadm hRB hR'B hRt hR't L ν Aν hA1 hA cν hJ cfr hcfr J hJl x hx y hy hy0 π hπ hdet
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      nsmul_eq_mul] at h
    rw [eΨ]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum] at h ⊢
    ring_nf at h ⊢
    linarith

  set aA : ℝ := (m : ℝ) * ((m + m') : ℕ) * Real.log 2 + (m : ℝ) * (|cA| * k) + ((m'.factorial : ℕ) : ℝ) * Real.log 2
    with haA
  set hv : NumberField.FinitePlace ↥L → ℝ := fun v => (m : ℝ) * (|cB| * k * ∑ p ∈ S, -Real.log (v (p : ↥L)))
    with hhv
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hinf : ∀ w : NumberField.InfinitePlace ↥L, Ψ w ≤ aA := by
    intro w
    have key := perplace w.val 2 (by norm_num) (ConfLedger.Glob.infinitePlace_add_le w) (cA * k) (hJa k L w)
    have h1 : (m : ℝ) * (cA * k) ≤ (m : ℝ) * (|cA| * k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self cA) hk) hm
    calc Ψ w = Ψ (w.val : ↥L → ℝ) := rfl
      _ ≤ _ := key
      _ ≤ aA := by rw [haA]; linarith
  have hfin : ∀ v ∈ T, Ψ v ≤ hv v := by
    intro v _
    have hsum_nonneg : 0 ≤ ∑ p ∈ S, -Real.log (v (p : ↥L)) :=
      Finset.sum_nonneg fun p hp => ConfLedger.Sum.neg_log_natCast_nonneg v p (hSprime p hp).ne_zero
    have hv_nonneg : 0 ≤ hv v := by
      rw [hhv]; exact mul_nonneg hm (mul_nonneg (mul_nonneg (abs_nonneg _) hk) hsum_nonneg)
    by_cases hgood : ∀ p ∈ S, v (p : ↥L) = 1
    · have key := perplace v.val 1 le_rfl (ConfLedger.Glob.finitePlace_add_le v) 0 (hJg k L v hgood)
      simp only [Real.log_one, mul_zero, zero_add, add_zero] at key
      calc Ψ v = Ψ (v.val : ↥L → ℝ) := rfl
        _ ≤ 0 := key
        _ ≤ hv v := hv_nonneg
    · push Not at hgood
      obtain ⟨p, hpS, hp1⟩ := hgood
      have hplt : v (p : ↥L) < 1 := lt_of_le_of_ne (ConfLedger.Sum.natCast_le_one v p) hp1
      have key := perplace v.val 1 le_rfl (ConfLedger.Glob.finitePlace_add_le v)
        (cB * k * (-Real.log (v (p : ↥L)))) (hJb k L v p (hSprime p hpS) hpS hplt)
      simp only [Real.log_one, mul_zero, zero_add, add_zero] at key
      have hlp : 0 ≤ -Real.log (v (p : ↥L)) := ConfLedger.Sum.neg_log_natCast_nonneg v p (hSprime p hpS).ne_zero
      have hsingle : -Real.log (v (p : ↥L)) ≤ ∑ p ∈ S, -Real.log (v (p : ↥L)) :=
        Finset.single_le_sum (fun p hp => ConfLedger.Sum.neg_log_natCast_nonneg v p (hSprime p hp).ne_zero) hpS
      have h2 : cB * k * (-Real.log (v (p : ↥L))) ≤ |cB| * k * ∑ p ∈ S, -Real.log (v (p : ↥L)) :=
        calc cB * k * (-Real.log (v (p : ↥L))) ≤ |cB| * k * (-Real.log (v (p : ↥L))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self cB) hk) hlp
          _ ≤ |cB| * k * ∑ p ∈ S, -Real.log (v (p : ↥L)) :=
              mul_le_mul_of_nonneg_left hsingle (mul_nonneg (abs_nonneg _) hk)
      calc Ψ v = Ψ (v.val : ↥L → ℝ) := rfl
        _ ≤ (m : ℝ) * (cB * k * (-Real.log (v (p : ↥L)))) := key
        _ ≤ hv v := by rw [hhv]; exact mul_le_mul_of_nonneg_left h2 hm

  have hbound := ConfLedger.Sum.PSL_le T Ψ aA hv hinf hfin
  set d : ℝ := (Module.finrank ℚ ↥L : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Module.finrank_pos
  have hsumT : ∑ v ∈ T, hv v = (m : ℝ) * (|cB| * k * (d * ∑ p ∈ S, Real.log p)) := by
    simp only [hhv]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    congr 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp =>
      ConfLedger.Sum.sum_neg_log_natCast T p (hSprime p hp).ne_zero (hTp p hp)
  rw [hsumT] at hbound

  have hxvec : ∀ w ∈ P, (fun l => ((x w l : ↥L) : AlgebraicClosure ℚ)) = evalVec s w := fun w hw => funext (hxP w hw)
  have hmnvec : ∀ o ∈ P, ∀ w ∈ P,
      (fun q : Fin r × Fin r => ((mn o w q : ↥L) : AlgebraicClosure ℚ)) = chordVec s o w := by
    intro o ho w hw
    funext q
    simp only [mn]
    push_cast
    rw [hxP o ho, hxP w hw, hxP o ho, hxP w hw]
    rfl
  have eLp : ∀ o ∈ P, ∀ w ∈ P, ConfLedger.Sum.PSL T (Lp o w) = d * pairHt s o w := by
    intro o ho w hw
    simp only [Lp, map_sub, map_add]
    rw [ConfLedger.Sum.PSL_La L (x o) T (hTx o ho), ConfLedger.Sum.PSL_La L (x w) T (hTx w hw),
      ConfLedger.Sum.PSL_La L (mn o w) T (hTmn o ho w hw), hxvec o ho, hxvec w hw, hmnvec o ho w hw]
    simp only [pairHt, pointHt, hd_def]
    ring
  have eG1 : ConfLedger.Sum.PSL T (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), Lp (R i) (R i'))
      = d * ∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i') := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => eLp _ (hPRl i) _ (hPRl i')
  have eG2 : ConfLedger.Sum.PSL T (∑ i : Fin m, ∑ i' : Fin m', Lp (R i) (R' i'))
      = d * ∑ i : Fin m, ∑ i' : Fin m', pairHt s (R i) (R' i') := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => eLp _ (hPRl i) _ (hPRr i')
  have eG3 : ConfLedger.Sum.PSL T (∑ i : Fin m, ∑ w ∈ B.support, ((B w : ℤ) : ℝ) • Lp (R i) w)
      = d * ∑ i : Fin m, B.sum (fun w n => (n : ℝ) * pairHt s (R i) w) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [LinearMap.map_smul, eLp _ (hPRl i) _ (hPB w hw), smul_eq_mul]
    ring
  have eG4 : ConfLedger.Sum.PSL T (∑ i : Fin m, ((((k : ℝ) - 2 * (e i : ℝ)) • ConfLedger.Sum.La (x (R i)))
        + (e i : ℝ) • ConfLedger.Sum.La (y (Fin.castAdd m' i))))
      = d * ∑ i : Fin m, (((k : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
          + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
              regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1))) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul, ConfLedger.Sum.PSL_La L (x (R i)) T (hTx _ (hPRl i)),
      ConfLedger.Sum.PSL_La L (y (Fin.castAdd m' i)) T (hTy _), hxvec _ (hPRl i)]
    have hyvec : (fun p => ((y (Fin.castAdd m' i) p : ↥L) : AlgebraicClosure ℚ))
        = fun p : Fin r × Fin r => regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1) := by
      funext p
      rw [hyv]
      simp only [hYtan, hRa, hta, Fin.append_left]
    rw [hyvec]
    simp only [pointHt, smul_eq_mul, hd_def]
    ring
  have eDet : ConfLedger.Sum.PSL T (ConfLedger.Sum.Lc J.det) = 0 := ConfLedger.Sum.PSL_Lc T J.det hTdet
  have eC : ConfLedger.Sum.PSL T (ConfLedger.Sum.La cvec) = d * absLogHeight (fun q : Fin (m + m') × (Fin k → Fin r) => c q.1 q.2) := by
    rw [ConfLedger.Sum.PSL_La L cvec T hTc]
  have eG5 : ConfLedger.Sum.PSL T (∑ i : Fin m, ConfLedger.Sum.Lc (π (Fin.castAdd m' i))) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => ConfLedger.Sum.PSL_Lc T _ (hTπ _)
  have eG6 : ConfLedger.Sum.PSL T (∑ i' : Fin m', ConfLedger.Sum.La (fun j => J (Fin.natAdd m i') j))
      = d * ∑ i' : Fin m', absLogHeight (fun j : Fin (m + m') => (R' i').taylorCoeff (t' i') (e' i') (u j)) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [ConfLedger.Sum.PSL_La L (fun j => J (Fin.natAdd m i') j) T (hTJ _)]
    have hrow : (fun j => ((J (Fin.natAdd m i') j : ↥L) : AlgebraicClosure ℚ))
        = fun j : Fin (m + m') => (R' i').taylorCoeff (t' i') (e' i') (u j) := by
      funext j
      rw [hJl, jetMatrix_apply]
      simp only [hRa, hta, hea, Fin.append_right]
    rw [hrow]
  have hId : ConfLedger.Sum.PSL T Ψ = d *
      ((∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i')) / 2
        + ∑ i : Fin m, ∑ i' : Fin m', pairHt s (R i) (R' i')
        + ∑ i : Fin m, B.sum (fun w n => (n : ℝ) * pairHt s (R i) w)
        - ∑ i : Fin m, (((k : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
            + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1)))
        - (m : ℝ) * absLogHeight (fun q : Fin (m + m') × (Fin k → Fin r) => c q.1 q.2)
        - ∑ i' : Fin m', absLogHeight (fun j : Fin (m + m') => (R' i').taylorCoeff (t' i') (e' i') (u j))) := by
    rw [hΨ]
    simp only [map_add, map_sub, LinearMap.map_smul, smul_eq_mul, eG1, eG2, eG3, eG4, eDet, eC, eG5, eG6]
    ring

  rw [hId] at hbound
  have hcH : (m : ℝ) * absLogHeight (fun q : Fin (m + m') × (Fin k → Fin r) => c q.1 q.2) ≤ (m : ℝ) * H :=
    mul_le_mul_of_nonneg_left hH hm
  have key : (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i')) / 2
        + ∑ i : Fin m, ∑ i' : Fin m', pairHt s (R i) (R' i')
        + ∑ i : Fin m, B.sum (fun w n => (n : ℝ) * pairHt s (R i) w)
        - ∑ i : Fin m, (((k : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
            + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1)))
        - (m : ℝ) * absLogHeight (fun q : Fin (m + m') × (Fin k → Fin r) => c q.1 q.2)
        - ∑ i' : Fin m', absLogHeight (fun j : Fin (m + m') => (R' i').taylorCoeff (t' i') (e' i') (u j))
      ≤ aA + (m : ℝ) * (|cB| * k * ∑ p ∈ S, Real.log p) := by
    refine le_of_mul_le_mul_left ?_ hd
    refine hbound.trans (le_of_eq ?_)
    ring
  rw [haA] at key
  ring_nf at key hcH ⊢
  linarith

end S_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix
end P2MW
export P2MW.S_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix (solution)
