-- Prove2me | solution 1 for ModularCurve.JZero.exists_seq_tendsto_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c3470a25-4752-593a-a602-91d8746cbd1c

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_ModularCurve_exists_seq_place_tendsto_evalAt_cuspInftyBar
import Theorems.Thm_ModularCurve_exists_seq_place_tendsto_evalAt
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_ModularCurve_JZero_chordVec_ne_zero_of_ne
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_seq_tendsto_place
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped KaehlerDifferential
open Filter Topology AlgebraicCurve ModularCurve

open Filter Topology

namespace SeqLimit

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def cprox (X Y : ι → ℂ) : ℝ :=
  Real.log (⨆ i, ‖X i‖) + Real.log (⨆ i, ‖Y i‖) - Real.log (⨆ p : ι × ι, ‖X p.1 * Y p.2 - X p.2 * Y p.1‖)

theorem tendsto_ciSup {α : Type*} {l : Filter α} {u : α → ι → ℝ} {a : ι → ℝ}
    (h : ∀ i, Tendsto (fun n => u n i) l (𝓝 (a i))) :
    Tendsto (fun n => ⨆ i, u n i) l (𝓝 (⨆ i, a i)) := by
  have e1 : ∀ v : ι → ℝ, (⨆ i, v i) = Finset.univ.sup' Finset.univ_nonempty v := fun v =>
    (Finset.sup'_univ_eq_ciSup v).symm
  simp only [e1]
  exact Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty fun i _ => h i

theorem ciSup_norm_ne_zero_iff {E : Type*} [NormedAddCommGroup E] (v : ι → E) :
    (⨆ i, ‖v i‖) ≠ 0 ↔ ∃ i, v i ≠ 0 := by
  have hbdd : BddAbove (Set.range fun i => ‖v i‖) := Set.finite_range _ |>.bddAbove
  constructor
  · intro h
    by_contra! h0
    apply h
    simp [h0]
  · rintro ⟨i, hi⟩ h0
    have hle : ‖v i‖ ≤ ⨆ j, ‖v j‖ := le_ciSup hbdd i
    rw [h0] at hle
    exact hi (norm_le_zero_iff.1 hle)

theorem ciSup_norm_nonneg {E : Type*} [NormedAddCommGroup E] (v : ι → E) : 0 ≤ ⨆ i, ‖v i‖ :=
  (norm_nonneg (v (Classical.arbitrary ι))).trans
    (le_ciSup (f := fun i => ‖v i‖) (Set.finite_range _ |>.bddAbove) (Classical.arbitrary ι))

theorem tendsto_limitAlgebra {X : ℕ → ι → ℂ} {A B : ι → ℂ} {c t : ℕ → ℂ} {ρ : ℂ} {k e : ℕ}
    (hX : ∀ i, Tendsto (fun n => (X n i - A i) / t n) atTop (𝓝 (B i)))
    (hc : Tendsto (fun n => c n / t n ^ e) atTop (𝓝 ρ)) (hρ : ρ ≠ 0)
    (ht : Tendsto t atTop (𝓝 0)) (ht0 : ∀ n, t n ≠ 0)
    (hA : (⨆ i, ‖A i‖) ≠ 0) (hAB : (⨆ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖) ≠ 0) :
    Tendsto (fun n => (k : ℝ) * Real.log (⨆ i, ‖X n i‖) - Real.log ‖c n‖ - (e : ℝ) * cprox (X n) A) atTop
      (𝓝 ((k : ℝ) * Real.log (⨆ i, ‖A i‖) - Real.log ‖ρ‖
        + (e : ℝ) * (Real.log (⨆ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖) - 2 * Real.log (⨆ i, ‖A i‖)))) := by

  set D : ℕ → ι × ι → ℂ := fun n p => (X n p.1 - A p.1) / t n * A p.2 - (X n p.2 - A p.2) / t n * A p.1 with hD
  have hDlim : ∀ p : ι × ι, Tendsto (fun n => D n p) atTop (𝓝 (B p.1 * A p.2 - B p.2 * A p.1)) := fun p =>
    ((hX p.1).mul tendsto_const_nhds).sub ((hX p.2).mul tendsto_const_nhds)
  have hminor : ∀ n (p : ι × ι), X n p.1 * A p.2 - X n p.2 * A p.1 = t n * D n p := by
    intro n p
    simp only [hD]
    field_simp [ht0 n]
    ring

  have hXA : ∀ i, Tendsto (fun n => X n i) atTop (𝓝 (A i)) := by
    intro i
    have h1 : Tendsto (fun n => t n * ((X n i - A i) / t n) + A i) atTop (𝓝 (0 * B i + A i)) :=
      (ht.mul (hX i)).add tendsto_const_nhds
    rw [zero_mul, zero_add] at h1
    refine h1.congr fun n => ?_
    rw [mul_div_cancel₀ _ (ht0 n), sub_add_cancel]

  have hSX : Tendsto (fun n => ⨆ i, ‖X n i‖) atTop (𝓝 (⨆ i, ‖A i‖)) :=
    tendsto_ciSup fun i => (hXA i).norm
  have hSD : Tendsto (fun n => ⨆ p : ι × ι, ‖D n p‖) atTop
      (𝓝 (⨆ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖)) := by
    have : ∀ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖ = ‖B p.1 * A p.2 - B p.2 * A p.1‖ := fun p => by
      rw [← norm_neg]; congr 1; ring
    simp only [this]
    exact tendsto_ciSup fun p => (hDlim p).norm
  have hSDne : ∀ᶠ n in atTop, (⨆ p : ι × ι, ‖D n p‖) ≠ 0 := hSD.eventually_ne hAB
  have hcne : ∀ᶠ n in atTop, c n / t n ^ e ≠ 0 := hc.eventually_ne hρ

  have hev : ∀ᶠ n in atTop,
      (k : ℝ) * Real.log (⨆ i, ‖X n i‖) - Real.log ‖c n‖ - (e : ℝ) * cprox (X n) A
        = ((k : ℝ) - e) * Real.log (⨆ i, ‖X n i‖) - Real.log ‖c n / t n ^ e‖
          - (e : ℝ) * Real.log (⨆ i, ‖A i‖) + (e : ℝ) * Real.log (⨆ p : ι × ι, ‖D n p‖) := by
    filter_upwards [hSDne, hcne] with n hDn hcn
    have htn : ‖t n‖ ≠ 0 := norm_ne_zero_iff.2 (ht0 n)
    have hM : (⨆ p : ι × ι, ‖X n p.1 * A p.2 - X n p.2 * A p.1‖) = ‖t n‖ * ⨆ p : ι × ι, ‖D n p‖ := by
      rw [Real.mul_iSup_of_nonneg (norm_nonneg _)]
      congr 1; funext p; rw [hminor, norm_mul]
    have hcn' : ‖c n‖ = ‖t n‖ ^ e * ‖c n / t n ^ e‖ := by
      rw [← norm_pow, ← norm_mul, mul_div_cancel₀ _ (pow_ne_zero _ (ht0 n))]
    simp only [cprox]
    rw [hM, hcn', Real.log_mul (pow_ne_zero _ htn) (norm_ne_zero_iff.2 hcn), Real.log_pow,
      Real.log_mul htn hDn]
    ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have h1 := hSX.log hA
  have h2 := hc.norm.log (norm_ne_zero_iff.2 hρ)
  have h3 := hSD.log hAB
  have h4 := (((tendsto_const_nhds (x := ((k : ℝ) - e))).mul h1).sub h2).sub
    (tendsto_const_nhds (x := (e : ℝ) * Real.log (⨆ i, ‖A i‖)))
  have h5 := h4.add ((tendsto_const_nhds (x := (e : ℝ))).mul h3)
  convert h5 using 2
  ring

end SeqLimit

namespace SeqLimit

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem tendsto_cprox {α : Type*} {l : Filter α} {X : α → ι → ℂ} {A Y : ι → ℂ}
    (hX : ∀ i, Tendsto (fun n => X n i) l (𝓝 (A i)))
    (hA : (⨆ i, ‖A i‖) ≠ 0) (hAY : (⨆ p : ι × ι, ‖A p.1 * Y p.2 - A p.2 * Y p.1‖) ≠ 0) :
    Tendsto (fun n => cprox (X n) Y) l (𝓝 (cprox A Y)) := by
  simp only [cprox]
  have h1 : Tendsto (fun n => ⨆ i, ‖X n i‖) l (𝓝 (⨆ i, ‖A i‖)) := tendsto_ciSup fun i => (hX i).norm
  have h3 : Tendsto (fun n => ⨆ p : ι × ι, ‖X n p.1 * Y p.2 - X n p.2 * Y p.1‖) l
      (𝓝 (⨆ p : ι × ι, ‖A p.1 * Y p.2 - A p.2 * Y p.1‖)) :=
    tendsto_ciSup fun p => (((hX p.1).mul tendsto_const_nhds).sub ((hX p.2).mul tendsto_const_nhds)).norm
  exact ((h1.log hA).add tendsto_const_nhds).sub (h3.log hAY)

theorem cprox_smul (c : ℂ) (hc : c ≠ 0) (X Y : ι → ℂ) (hX : (⨆ i, ‖X i‖) ≠ 0)
    (hXY : (⨆ p : ι × ι, ‖X p.1 * Y p.2 - X p.2 * Y p.1‖) ≠ 0) :
    cprox (c • X) Y = cprox X Y := by
  simp only [cprox, Pi.smul_apply, smul_eq_mul]
  have e1 : (⨆ i, ‖c * X i‖) = ‖c‖ * ⨆ i, ‖X i‖ := by
    rw [Real.mul_iSup_of_nonneg (norm_nonneg _)]; simp_rw [norm_mul]
  have e2 : (⨆ p : ι × ι, ‖c * X p.1 * Y p.2 - c * X p.2 * Y p.1‖) = ‖c‖ * ⨆ p : ι × ι, ‖X p.1 * Y p.2 - X p.2 * Y p.1‖ := by
    rw [Real.mul_iSup_of_nonneg (norm_nonneg _)]
    congr 1; funext p; rw [← norm_mul]; congr 1; ring
  rw [e1, e2, Real.log_mul (norm_ne_zero_iff.2 hc) hX, Real.log_mul (norm_ne_zero_iff.2 hc) hXY]
  ring

theorem pivot_change (c : ℂ) (hc : c ≠ 0) (X A : ι → ℂ) (s : ℂ) (hs : s ≠ 0) (k e : ℕ) (hX : (⨆ i, ‖X i‖) ≠ 0)
    (hXA : (⨆ p : ι × ι, ‖X p.1 * A p.2 - X p.2 * A p.1‖) ≠ 0) :
    (k : ℝ) * Real.log (⨆ i, ‖(c • X) i‖) - Real.log ‖s * c ^ k‖ - (e : ℝ) * cprox (c • X) A
      = (k : ℝ) * Real.log (⨆ i, ‖X i‖) - Real.log ‖s‖ - (e : ℝ) * cprox X A := by
  rw [cprox_smul c hc X A hX hXA]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : (⨆ i, ‖c * X i‖) = ‖c‖ * ⨆ i, ‖X i‖ := by
    rw [Real.mul_iSup_of_nonneg (norm_nonneg _)]; simp_rw [norm_mul]
  rw [e1, Real.log_mul (norm_ne_zero_iff.2 hc) hX, norm_mul, norm_pow,
    Real.log_mul (norm_ne_zero_iff.2 hs) (pow_ne_zero _ (norm_ne_zero_iff.2 hc)), Real.log_pow]
  ring

end SeqLimit

namespace SeqLimit

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem eventually_minors_ne_zero {X : ℕ → ι → ℂ} {A B : ι → ℂ} {t : ℕ → ℂ}
    (hX : ∀ i, Tendsto (fun n => (X n i - A i) / t n) atTop (𝓝 (B i)))
    (ht0 : ∀ n, t n ≠ 0)
    (hAB : (⨆ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖) ≠ 0) :
    ∀ᶠ n in atTop, (⨆ p : ι × ι, ‖X n p.1 * A p.2 - X n p.2 * A p.1‖) ≠ 0 := by
  set D : ℕ → ι × ι → ℂ := fun n p => (X n p.1 - A p.1) / t n * A p.2 - (X n p.2 - A p.2) / t n * A p.1 with hD
  have hDlim : ∀ p : ι × ι, Tendsto (fun n => D n p) atTop (𝓝 (B p.1 * A p.2 - B p.2 * A p.1)) := fun p =>
    ((hX p.1).mul tendsto_const_nhds).sub ((hX p.2).mul tendsto_const_nhds)
  have hminor : ∀ n (p : ι × ι), X n p.1 * A p.2 - X n p.2 * A p.1 = t n * D n p := by
    intro n p
    simp only [hD]
    field_simp [ht0 n]
    ring
  have hSD : Tendsto (fun n => ⨆ p : ι × ι, ‖D n p‖) atTop
      (𝓝 (⨆ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖)) := by
    have : ∀ p : ι × ι, ‖A p.1 * B p.2 - A p.2 * B p.1‖ = ‖B p.1 * A p.2 - B p.2 * A p.1‖ := fun p => by
      rw [← norm_neg]; congr 1; ring
    simp only [this]
    exact tendsto_ciSup fun p => (hDlim p).norm
  filter_upwards [hSD.eventually_ne hAB] with n hDn
  have hM : (⨆ p : ι × ι, ‖X n p.1 * A p.2 - X n p.2 * A p.1‖) = ‖t n‖ * ⨆ p : ι × ι, ‖D n p‖ := by
    rw [Real.mul_iSup_of_nonneg (norm_nonneg _)]
    congr 1; funext p; rw [hminor, norm_mul]
  rw [hM]
  exact mul_ne_zero (norm_ne_zero_iff.2 (ht0 n)) hDn

end SeqLimit

namespace SeqLocal

section PlaceAPI
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  simpa using AlgebraicCurve.Place.evalAt_algebraMap v (0 : K)

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_neg (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add v hv hf (neg_mem hg), evalAt_neg v hv hg, ← sub_eq_add_neg]

theorem evalAt_pow (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [AlgebraicCurve.Place.evalAt_one]
  | succ n ih => rw [pow_succ, AlgebraicCurve.Place.evalAt_mul v hv (pow_mem hf n) hf, ih, pow_succ]

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : 0 < v.ord f) :
    v.evalAt f = 0 := by
  rw [← evalAt_zero v]
  exact AlgebraicCurve.Place.evalAt_congr v hf (zero_mem _) (Or.inr (by simpa using h))

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra hne
  exact h (evalAt_eq_zero_of_ord_pos v hf (lt_of_le_of_ne (AlgebraicCurve.Place.ord_nonneg_of_mem v hf) (Ne.symm hne)))

theorem sub_evalAt_eq_zero_or_ord_pos (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    f - algebraMap K F (v.evalAt f) = 0 ∨ 0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  by_cases h0 : f - algebraMap K F (v.evalAt f) = 0
  · exact Or.inl h0
  · right
    have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' _)
    rcases (AlgebraicCurve.Place.ord_nonneg_of_mem v hmem).eq_or_lt with h | h
    · exfalso
      apply AlgebraicCurve.Place.evalAt_ne_zero v hv h0 h.symm
      rw [evalAt_sub v hv hf (v.algebraMap_mem' _), AlgebraicCurve.Place.evalAt_algebraMap, sub_self]
    · exact h

end PlaceAPI

variable (N : ℕ) [NeZero N]

theorem isRational (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mp
    (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)

variable {N}

theorem embDivisor_apply_cuspInftyBar : embDivisor N (cuspInftyBar N) = embDegree N := by
  simp [embDivisor]

theorem embDivisor_nonneg (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : 0 ≤ embDivisor N w := by
  classical
  simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  split_ifs <;> simp

theorem IsEmbBasis.pos {r : ℕ} {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with h | h
  · exfalso
    subst h
    have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
      rw [mem_riemannRochSpace_iff]
      intro w
      right
      rw [w.ord_one, neg_nonpos]
      exact embDivisor_nonneg w
    rw [← hs.2, Set.range_eq_empty s, Submodule.span_empty, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

namespace IsEmbBasis
private theorem _root_.SeqLocal.IsEmbBasis.ne_zero {r : ℕ} {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r) : s i ≠ 0 :=
  hs.1.ne_zero i

end IsEmbBasis
p2m_export "SeqLocal" "IsEmbBasis.ne_zero"
theorem ord_pivotIndex_le {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) (j : Fin r) :
    w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => w.ord (s i)) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  simp only [pivotIndex, dif_pos hex]
  exact Classical.choose_spec hex j

theorem ord_pivotIndex_cuspInftyBar {r : ℕ} {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (hr : 0 < r) :
    (cuspInftyBar N).ord (s (pivotIndex s (cuspInftyBar N) hr)) = -(embDegree N : ℤ) := by
  obtain ⟨i, hi⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs (cuspInftyBar N)
  rw [embDivisor_apply_cuspInftyBar] at hi
  apply le_antisymm
  · have := ord_pivotIndex_le s (cuspInftyBar N) hr i
    omega
  · have hmem : s (pivotIndex s (cuspInftyBar N) hr) ∈ riemannRochSpace (embDivisor N) := by
      rw [← hs.2]; exact Submodule.subset_span ⟨_, rfl⟩
    rcases (mem_riemannRochSpace_iff.mp hmem) (cuspInftyBar N) with h0 | h
    · exact absurd h0 (IsEmbBasis.ne_zero hs _)
    · rwa [embDivisor_apply_cuspInftyBar] at h

set_option maxHeartbeats 6400000 in

theorem exists_mem_riemannRochSpace_ord_eq (N : ℕ) [NeZero N] :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧ f ∈ riemannRochSpace (embDivisor N) ∧
      (cuspInftyBar N).ord f = -(2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ)) := by
  classical
  set O := cuspInftyBar N with hO
  set g : ℕ := genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) with hg
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI hcan : AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  obtain ⟨x, hx⟩ := AlgebraicCurve.exists_D_ne_zero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar N
  have hgen : (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) = g := by
    exact_mod_cast ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N
  have hK := ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar N hx
  have hdegO : (O.deg : ℤ) = 1 := by exact_mod_cast ModularCurve.deg_eq_one_modularFunctionFieldBar N O
  set D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := (2 * (g : ℤ)) • Finsupp.single O 1 with hD₁
  set D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := (2 * (g : ℤ) - 1) • Finsupp.single O 1 with hD₂
  have hdeg₁ : D₁.degree = 2 * g := by rw [hD₁, map_zsmul, Divisor.degree_single, hdegO, smul_eq_mul]; ring
  have hdeg₂ : D₂.degree = 2 * g - 1 := by rw [hD₂, map_zsmul, Divisor.degree_single, hdegO, smul_eq_mul]; ring
  have hell₁ : (ell D₁ : ℤ) = g + 1 := by
    have h := hRR hx D₁
    have h0 : ell (AlgebraicCurve.canonicalDivisorOf hx - D₁) = 0 :=
      AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub, hK, hdeg₁, hgen]; omega)
    rw [h0, hdeg₁, hgen] at h
    push_cast at h
    linarith
  have hell₂ : (ell D₂ : ℤ) = g := by
    have h := hRR hx D₂
    have h0 : ell (AlgebraicCurve.canonicalDivisorOf hx - D₂) = 0 :=
      AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub, hK, hdeg₂, hgen]; omega)
    rw [h0, hdeg₂, hgen] at h
    push_cast at h
    linarith
  have hD₁O : D₁ O = 2 * g := by simp [hD₁]
  have hD₂O : D₂ O = 2 * g - 1 := by simp [hD₂]
  have hD₁v : ∀ v, v ≠ O → D₁ v = 0 := fun v hv => by simp [hD₁, Finsupp.single_apply, Ne.symm hv]
  have hD₂v : ∀ v, v ≠ O → D₂ v = 0 := fun v hv => by simp [hD₂, Finsupp.single_apply, Ne.symm hv]
  have hle : riemannRochSpace D₂ ≤ riemannRochSpace D₁ := by
    refine AlgebraicCurve.lSpace_mono (fun v => ?_)
    by_cases hv : v = O
    · subst hv; rw [hD₁O, hD₂O]; omega
    · rw [hD₁v v hv, hD₂v v hv]
  have hlt : riemannRochSpace D₂ < riemannRochSpace D₁ := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank hle ?_
    have e1 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D₁) = ell D₁ := rfl
    have e2 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D₂) = ell D₂ := rfl
    rw [e1, e2]
    omega
  obtain ⟨f, hf₁, hf₂⟩ := SetLike.exists_of_lt hlt
  have hf0 : f ≠ 0 := by rintro rfl; exact hf₂ (zero_mem _)
  refine ⟨f, hf0, AlgebraicCurve.lSpace_mono (fun v => ?_) hf₁, ?_⟩
  · by_cases hv : v = O
    · subst hv
      rw [hD₁O, show embDivisor N O = embDegree N from embDivisor_apply_cuspInftyBar]
      simp only [embDegree]
      rw [hg]
      push_cast
      omega
    · rw [hD₁v v hv]; exact embDivisor_nonneg v
  · rw [mem_riemannRochSpace_iff] at hf₁ hf₂
    push_neg at hf₂
    obtain ⟨v, -, hv⟩ := hf₂
    have h1 := (hf₁ O).resolve_left hf0
    rw [hD₁O] at h1
    by_cases hvO : v = O
    · subst hvO
      rw [hD₂O] at hv
      omega
    · have := (hf₁ v).resolve_left hf0
      rw [hD₁v v hvO] at this
      rw [hD₂v v hvO] at hv
      omega

set_option maxHeartbeats 6400000 in

theorem exists_evalAt_firstOrder_ne_zero {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) (hr : 0 < r) :
    ∃ i : Fin r, (cuspInftyBar N).evalAt
      ((s i * (s (pivotIndex s (cuspInftyBar N) hr))⁻¹
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            ((cuspInftyBar N).evalAt (s i * (s (pivotIndex s (cuspInftyBar N) hr))⁻¹))) * t⁻¹) ≠ 0 := by
  classical
  set O := cuspInftyBar N with hO
  have hrat : O.IsRational := isRational N O
  set π := pivotIndex s O hr with hπ
  have hs0 : ∀ i, s i ≠ 0 := IsEmbBasis.ne_zero hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hπord : O.ord (s π) = -(embDegree N : ℤ) := ord_pivotIndex_cuspInftyBar hs hr
  set x : Fin r → modularFunctionFieldBar N := fun i => s i * (s π)⁻¹ with hx
  have hx0 : ∀ i, x i ≠ 0 := fun i => mul_ne_zero (hs0 i) (inv_ne_zero (hs0 π))
  have hxO : ∀ i, x i ∈ O.toValuationSubring := fun i => by
    refine AlgebraicCurve.Place.mem_of_ord_nonneg O (hx0 i) ?_
    show 0 ≤ O.ord (s i * (s π)⁻¹)
    rw [O.ord_mul (hs0 i) (inv_ne_zero (hs0 π)), O.ord_inv]
    have := ord_pivotIndex_le s O hr i
    rw [← hπ] at this
    omega
  set w : Fin r → modularFunctionFieldBar N :=
    fun i => x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i)) with hw
  by_contra hall
  push_neg at hall
  change ∀ i, O.evalAt (w i * t⁻¹) = 0 at hall

  have hw2 : ∀ i, w i = 0 ∨ 2 ≤ O.ord (w i) := by
    intro i
    rcases sub_evalAt_eq_zero_or_ord_pos O hrat (hxO i) with h0 | hpos
    · exact Or.inl h0
    · right
      have hwne : w i ≠ 0 := fun h => by
        change x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i)) = 0 at h
        rw [h] at hpos; simp at hpos
      have hy0 : w i * t⁻¹ ≠ 0 := mul_ne_zero hwne (inv_ne_zero ht0)
      have hyord : O.ord (w i * t⁻¹) = O.ord (w i) - 1 := by
        rw [O.ord_mul hwne (inv_ne_zero ht0), O.ord_inv, ht]; ring
      have hpos' : 0 < O.ord (w i) := hpos
      have hymem : w i * t⁻¹ ∈ O.toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg O hy0 (by rw [hyord]; omega)
      have hne : O.ord (w i * t⁻¹) ≠ 0 := fun h => (AlgebraicCurve.Place.evalAt_ne_zero O hrat hy0 h) (hall i)
      have hnn : 0 ≤ O.ord (w i * t⁻¹) := AlgebraicCurve.Place.ord_nonneg_of_mem O hymem
      omega

  obtain ⟨f, hf0, hfE, hford⟩ := exists_mem_riemannRochSpace_ord_eq N
  rw [← hs.2] at hfE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hfE
  set Cst : AlgebraicClosure ℚ := ∑ i, c i * O.evalAt (x i) with hCst
  set R : modularFunctionFieldBar N := ∑ i, c i • w i with hR
  have hdecomp : f * (s π)⁻¹ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) Cst + R := by
    rw [← hc, Finset.sum_mul, hCst, hR, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hw, hx, Algebra.smul_def, map_mul]
    ring
  have h1 : O.ord (f * (s π)⁻¹) = 1 := by
    rw [O.ord_mul hf0 (inv_ne_zero (hs0 π)), O.ord_inv, hπord, hford]
    simp only [embDegree]
    push_cast
    ring

  have hR2 : R = 0 ∨ 2 ≤ O.ord R := by
    have hval : O.adicValuation R ≤ WithZero.exp (-2 : ℤ) := by
      rw [hR]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      rcases hw2 i with h0 | h2
      · simp [h0]
      · calc O.adicValuation (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c i)) * O.adicValuation (w i)
            ≤ 1 * O.adicValuation (w i) := mul_le_mul_left (O.adicValuation_algebraMap_le_one _) _
          _ ≤ WithZero.exp (-2 : ℤ) := by
              rw [one_mul, O.adicValuation_le_exp_iff]
              right; simpa using h2
    have := (O.adicValuation_le_exp_iff).mp hval
    simpa using this

  have hordC : Cst ≠ 0 → O.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) Cst) = 0 := fun hC => by
    have h₁ := AlgebraicCurve.Place.ord_nonneg_of_mem O (O.algebraMap_mem' Cst)
    have h₂ := AlgebraicCurve.Place.ord_nonneg_of_mem O (O.algebraMap_mem' Cst⁻¹)
    rw [map_inv₀, O.ord_inv] at h₂
    omega

  rw [hdecomp] at h1
  rcases hR2 with hR0 | hR2'
  · rw [hR0, add_zero] at h1
    by_cases hC : Cst = 0
    · rw [hC, map_zero, O.ord_zero] at h1; exact zero_ne_one h1
    · rw [hordC hC] at h1; exact zero_ne_one h1
  · have hRne : R ≠ 0 := fun h => by rw [h, O.ord_zero] at hR2'; omega
    by_cases hC : Cst = 0
    · rw [hC, map_zero, zero_add] at h1; omega
    ·
      have hsum0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) Cst + R ≠ 0 := fun h => by
        rw [h, O.ord_zero] at h1; exact zero_ne_one h1
      have hnegR : O.ord (-R) = O.ord R := by simp only [AlgebraicCurve.Place.ord, Valuation.map_neg]
      have key := AlgebraicCurve.Place.min_ord_le_ord_add O hsum0 (neg_ne_zero.2 hRne)
        (by rw [add_neg_cancel_right]; exact (map_ne_zero _).2 hC)
      rw [add_neg_cancel_right, hordC hC, h1, hnegR] at key
      omega

theorem exists_forall_norm_apply_le (α : AlgebraicClosure ℚ) : ∃ M : ℝ, 0 < M ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, ‖σ α‖ ≤ M := by
  classical
  set p : Polynomial ℚ := minpoly ℚ α with hp
  have hpne : p ≠ 0 := minpoly.ne_zero ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic α).isIntegral
  refine ⟨1 + ∑ z ∈ (p.aroots ℂ).toFinset, ‖z‖, by positivity, fun σ => ?_⟩
  have hroot : σ α ∈ (p.aroots ℂ).toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
    refine ⟨hpne, ?_⟩
    have h1 : Polynomial.aeval (σ.toRatAlgHom α) p = σ.toRatAlgHom (Polynomial.aeval α p) :=
      Polynomial.aeval_algHom_apply σ.toRatAlgHom α p
    rw [hp] at h1 ⊢
    simpa [minpoly.aeval] using h1
  have := Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun z _ => norm_nonneg z) hroot
  linarith

theorem exists_forall_le_norm_apply {α : AlgebraicClosure ℚ} (hα : α ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, m ≤ ‖σ α‖ := by
  obtain ⟨M, hM, h⟩ := exists_forall_norm_apply_le α⁻¹
  refine ⟨M⁻¹, inv_pos.2 hM, fun σ => ?_⟩
  have hσ : σ α ≠ 0 := (map_ne_zero σ).2 hα
  have := h σ
  rw [map_inv₀, norm_inv] at this
  rw [inv_le_comm₀ hM (norm_pos_iff.2 hσ)]
  exact this

theorem prox_eq_cprox {r : ℕ} [Nonempty (Fin r)] (σ : AlgebraicClosure ℚ →+* ℂ) (x y : Fin r → AlgebraicClosure ℚ) :
    prox (fun a => ‖σ a‖) x y = SeqLimit.cprox (fun i => σ (x i)) (fun i => σ (y i)) := by
  simp only [prox, SeqLimit.cprox, map_sub, map_mul]

end SeqLocal

namespace SeqLocal

variable {N : ℕ} [NeZero N]

theorem ord_pivotIndex_eq {r : ℕ} {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (hr : 0 < r)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    w.ord (s (pivotIndex s w hr)) = -(embDivisor N w) := by
  obtain ⟨i, hi⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs w
  apply le_antisymm
  · have := ord_pivotIndex_le s w hr i
    omega
  · have hmem : s (pivotIndex s w hr) ∈ riemannRochSpace (embDivisor N) := by
      rw [← hs.2]; exact Submodule.subset_span ⟨_, rfl⟩
    rcases (mem_riemannRochSpace_iff.mp hmem) w with h0 | h
    · exact absurd h0 (IsEmbBasis.ne_zero hs _)
    · exact h

set_option maxHeartbeats 6400000 in

theorem exists_mem_riemannRochSpace_ord_add_eq_one (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧ f ∈ riemannRochSpace (embDivisor N) ∧ w.ord f + embDivisor N w = 1 := by
  classical
  set g : ℕ := genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) with hg
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI hcan : AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  obtain ⟨x, hx⟩ := AlgebraicCurve.exists_D_ne_zero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar N
  have hgen : (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) = g := by
    exact_mod_cast ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N
  have hK := ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar N hx
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), (v.deg : ℤ) = 1 := fun v => by
    exact_mod_cast ModularCurve.deg_eq_one_modularFunctionFieldBar N v
  have hdegE : (embDivisor N).degree = 2 * g + 1 := by
    simp only [embDivisor, embDegree, map_zsmul, Divisor.degree_single, hdeg1, smul_eq_mul, mul_one]
    rw [hg]; push_cast; ring
  set D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := embDivisor N - Finsupp.single w 1 with hD₁
  set D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := embDivisor N - Finsupp.single w 2 with hD₂
  have hdeg₁ : D₁.degree = 2 * g := by rw [hD₁, map_sub, hdegE, Divisor.degree_single, hdeg1]; ring
  have hdeg₂ : D₂.degree = 2 * g - 1 := by rw [hD₂, map_sub, hdegE, Divisor.degree_single, hdeg1]; ring
  have hell₁ : (ell D₁ : ℤ) = g + 1 := by
    have h := hRR hx D₁
    have h0 : ell (AlgebraicCurve.canonicalDivisorOf hx - D₁) = 0 :=
      AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub, hK, hdeg₁, hgen]; omega)
    rw [h0, hdeg₁, hgen] at h
    push_cast at h
    linarith
  have hell₂ : (ell D₂ : ℤ) = g := by
    have h := hRR hx D₂
    have h0 : ell (AlgebraicCurve.canonicalDivisorOf hx - D₂) = 0 :=
      AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub, hK, hdeg₂, hgen]; omega)
    rw [h0, hdeg₂, hgen] at h
    push_cast at h
    linarith
  have hD₁w : D₁ w = embDivisor N w - 1 := by simp [hD₁]
  have hD₂w : D₂ w = embDivisor N w - 2 := by simp [hD₂]
  have hD₁v : ∀ v, v ≠ w → D₁ v = embDivisor N v := fun v hv => by simp [hD₁, Finsupp.single_apply, Ne.symm hv]
  have hD₂v : ∀ v, v ≠ w → D₂ v = embDivisor N v := fun v hv => by simp [hD₂, Finsupp.single_apply, Ne.symm hv]
  have hle : riemannRochSpace D₂ ≤ riemannRochSpace D₁ := by
    refine AlgebraicCurve.lSpace_mono (fun v => ?_)
    by_cases hv : v = w
    · subst hv; rw [hD₁w, hD₂w]; omega
    · rw [hD₁v v hv, hD₂v v hv]
  have hlt : riemannRochSpace D₂ < riemannRochSpace D₁ := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank hle ?_
    have e1 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D₁) = ell D₁ := rfl
    have e2 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D₂) = ell D₂ := rfl
    rw [e1, e2]
    omega
  obtain ⟨f, hf₁, hf₂⟩ := SetLike.exists_of_lt hlt
  have hf0 : f ≠ 0 := by rintro rfl; exact hf₂ (zero_mem _)
  refine ⟨f, hf0, AlgebraicCurve.lSpace_mono (fun v => ?_) hf₁, ?_⟩
  · by_cases hv : v = w
    · subst hv; rw [hD₁w]; omega
    · rw [hD₁v v hv]
  · rw [mem_riemannRochSpace_iff] at hf₁ hf₂
    push_neg at hf₂
    obtain ⟨v, -, hv⟩ := hf₂
    have h1 := (hf₁ w).resolve_left hf0
    rw [hD₁w] at h1
    by_cases hvw : v = w
    · subst hvw
      rw [hD₂w] at hv
      omega
    · have := (hf₁ v).resolve_left hf0
      rw [hD₁v v hvw] at this
      rw [hD₂v v hvw] at hv
      omega

set_option maxHeartbeats 6400000 in

theorem exists_evalAt_firstOrder_ne_zero_at {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (t : modularFunctionFieldBar N) (ht : w.ord t = 1) (hr : 0 < r) :
    ∃ i : Fin r, w.evalAt
      ((s i * (s (pivotIndex s w hr))⁻¹
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (w.evalAt (s i * (s (pivotIndex s w hr))⁻¹))) * t⁻¹) ≠ 0 := by
  classical
  set O := w with hO
  have hrat : O.IsRational := isRational N O
  set π := pivotIndex s O hr with hπ
  have hs0 : ∀ i, s i ≠ 0 := IsEmbBasis.ne_zero hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hπord : O.ord (s π) = -(embDivisor N O) := ord_pivotIndex_eq hs hr O
  set x : Fin r → modularFunctionFieldBar N := fun i => s i * (s π)⁻¹ with hx
  have hx0 : ∀ i, x i ≠ 0 := fun i => mul_ne_zero (hs0 i) (inv_ne_zero (hs0 π))
  have hxO : ∀ i, x i ∈ O.toValuationSubring := fun i => by
    refine AlgebraicCurve.Place.mem_of_ord_nonneg O (hx0 i) ?_
    show 0 ≤ O.ord (s i * (s π)⁻¹)
    rw [O.ord_mul (hs0 i) (inv_ne_zero (hs0 π)), O.ord_inv]
    have := ord_pivotIndex_le s O hr i
    rw [← hπ] at this
    omega
  set wv : Fin r → modularFunctionFieldBar N :=
    fun i => x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i)) with hw
  by_contra hall
  push_neg at hall
  change ∀ i, O.evalAt (wv i * t⁻¹) = 0 at hall
  have hw2 : ∀ i, wv i = 0 ∨ 2 ≤ O.ord (wv i) := by
    intro i
    rcases sub_evalAt_eq_zero_or_ord_pos O hrat (hxO i) with h0 | hpos
    · exact Or.inl h0
    · right
      have hwne : wv i ≠ 0 := fun h => by
        change x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i)) = 0 at h
        rw [h] at hpos; simp at hpos
      have hy0 : wv i * t⁻¹ ≠ 0 := mul_ne_zero hwne (inv_ne_zero ht0)
      have hyord : O.ord (wv i * t⁻¹) = O.ord (wv i) - 1 := by
        rw [O.ord_mul hwne (inv_ne_zero ht0), O.ord_inv, ht]; ring
      have hpos' : 0 < O.ord (wv i) := hpos
      have hymem : wv i * t⁻¹ ∈ O.toValuationSubring :=
        AlgebraicCurve.Place.mem_of_ord_nonneg O hy0 (by rw [hyord]; omega)
      have hne : O.ord (wv i * t⁻¹) ≠ 0 := fun h => (AlgebraicCurve.Place.evalAt_ne_zero O hrat hy0 h) (hall i)
      have hnn : 0 ≤ O.ord (wv i * t⁻¹) := AlgebraicCurve.Place.ord_nonneg_of_mem O hymem
      omega
  obtain ⟨f, hf0, hfE, hford⟩ := exists_mem_riemannRochSpace_ord_add_eq_one N O
  rw [← hs.2] at hfE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hfE
  set Cst : AlgebraicClosure ℚ := ∑ i, c i * O.evalAt (x i) with hCst
  set R : modularFunctionFieldBar N := ∑ i, c i • wv i with hR
  have hdecomp : f * (s π)⁻¹ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) Cst + R := by
    rw [← hc, Finset.sum_mul, hCst, hR, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hw, hx, Algebra.smul_def, map_mul]
    ring
  have h1 : O.ord (f * (s π)⁻¹) = 1 := by
    rw [O.ord_mul hf0 (inv_ne_zero (hs0 π)), O.ord_inv, hπord]
    omega
  have hR2 : R = 0 ∨ 2 ≤ O.ord R := by
    have hval : O.adicValuation R ≤ WithZero.exp (-2 : ℤ) := by
      rw [hR]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      rcases hw2 i with h0 | h2
      · simp [h0]
      · calc O.adicValuation (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c i)) * O.adicValuation (wv i)
            ≤ 1 * O.adicValuation (wv i) := mul_le_mul_left (O.adicValuation_algebraMap_le_one _) _
          _ ≤ WithZero.exp (-2 : ℤ) := by
              rw [one_mul, O.adicValuation_le_exp_iff]
              right; simpa using h2
    have := (O.adicValuation_le_exp_iff).mp hval
    simpa using this
  have hordC : Cst ≠ 0 → O.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) Cst) = 0 := fun hC => by
    have h₁ := AlgebraicCurve.Place.ord_nonneg_of_mem O (O.algebraMap_mem' Cst)
    have h₂ := AlgebraicCurve.Place.ord_nonneg_of_mem O (O.algebraMap_mem' Cst⁻¹)
    rw [map_inv₀, O.ord_inv] at h₂
    omega
  rw [hdecomp] at h1
  rcases hR2 with hR0 | hR2'
  · rw [hR0, add_zero] at h1
    by_cases hC : Cst = 0
    · rw [hC, map_zero, O.ord_zero] at h1; exact zero_ne_one h1
    · rw [hordC hC] at h1; exact zero_ne_one h1
  · have hRne : R ≠ 0 := fun h => by rw [h, O.ord_zero] at hR2'; omega
    by_cases hC : Cst = 0
    · rw [hC, map_zero, zero_add] at h1; omega
    · have hsum0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) Cst + R ≠ 0 := fun h => by
        rw [h, O.ord_zero] at h1; exact zero_ne_one h1
      have hnegR : O.ord (-R) = O.ord R := by simp only [AlgebraicCurve.Place.ord, Valuation.map_neg]
      have key := AlgebraicCurve.Place.min_ord_le_ord_add O hsum0 (neg_ne_zero.2 hRne)
        (by rw [add_neg_cancel_right]; exact (map_ne_zero _).2 hC)
      rw [add_neg_cancel_right, hordC hC, h1, hnegR] at key
      omega

end SeqLocal

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (ht : v₀.ord t = 1)
    (hv₀ : v₀ = cuspInftyBar N ∨
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ v₀.toValuationSubring) :
    ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
      (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ e : ℕ, (e : ℤ) = v₀.ord u + k * embDivisor N v₀ →
      ∃ v : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ v₀) ∧
        (∀ w ∈ S, w ≠ v₀ →
          Filter.Tendsto (fun n => prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s w))
            Filter.atTop (nhds (prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w)))) ∧
        Filter.Tendsto (fun n => (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖)
            - Real.log ‖σ (secVal s (v n) k u)‖
            - (e : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s v₀))
          Filter.atTop (nhds (((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
            + (e : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1))‖)
            - Real.log ‖σ (regVal s v₀ t k e u)‖)) := by
  classical

  intro σ S k u hu huL e he
  set O := v₀ with hO
  have hr : 0 < r := SeqLocal.IsEmbBasis.pos hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hrat : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational := SeqLocal.isRational N
  set π : Fin r := pivotIndex s O hr with hπ
  have hs0 : ∀ i, s i ≠ 0 := SeqLocal.IsEmbBasis.ne_zero hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hπord : O.ord (s π) = -(embDivisor N O) := SeqLocal.ord_pivotIndex_eq hs hr O

  set x : Fin r → modularFunctionFieldBar N := fun i => s i * (s π)⁻¹ with hx
  have hx0 : ∀ i, x i ≠ 0 := fun i => mul_ne_zero (hs0 i) (inv_ne_zero (hs0 π))
  have hxO : ∀ i, x i ∈ O.toValuationSubring := fun i => by
    refine AlgebraicCurve.Place.mem_of_ord_nonneg O (hx0 i) ?_
    show 0 ≤ O.ord (s i * (s π)⁻¹)
    rw [O.ord_mul (hs0 i) (inv_ne_zero (hs0 π)), O.ord_inv]
    have := SeqLocal.ord_pivotIndex_le s O hr i
    rw [← hπ] at this
    omega
  have hxπ : x π = 1 := mul_inv_cancel₀ (hs0 π)
  set a : Fin r → AlgebraicClosure ℚ := fun i => O.evalAt (x i) with ha
  have hev : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r),
      evalVec s w i = w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) := fun w i => by
    simp only [evalVec, dif_pos hr]
  have haO : evalVec s O = a := by funext i; rw [hev]
  have haπ : a π = 1 := by simp only [ha, hxπ, AlgebraicCurve.Place.evalAt_one]
  set y : Fin r → modularFunctionFieldBar N :=
    fun i => (x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a i)) * t⁻¹ with hy
  have hyO : ∀ i, y i ∈ O.toValuationSubring := fun i => by
    rcases SeqLocal.sub_evalAt_eq_zero_or_ord_pos O (hrat O) (hxO i) with h0 | hpos
    · have : y i = 0 := by
        show (x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i))) * t⁻¹ = 0
        rw [h0, zero_mul]
      rw [this]; exact zero_mem _
    · have hne : x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i)) ≠ 0 := by
        intro h; rw [h] at hpos; simp at hpos
      refine AlgebraicCurve.Place.mem_of_ord_nonneg O (mul_ne_zero hne (inv_ne_zero ht0)) ?_
      show 0 ≤ O.ord ((x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (O.evalAt (x i))) * t⁻¹)
      rw [O.ord_mul hne (inv_ne_zero ht0), O.ord_inv, ht]
      omega
  have hyπ : y π = 0 := by
    show (x π - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a π)) * t⁻¹ = 0
    rw [haπ, hxπ, map_one, sub_self, zero_mul]
  set b : Fin r → AlgebraicClosure ℚ := fun i => O.evalAt (y i) with hb
  have hbπ : b π = 0 := by simp only [hb, hyπ, SeqLocal.evalAt_zero]

  obtain ⟨i₀, hi₀⟩ := SeqLocal.exists_evalAt_firstOrder_ne_zero_at s hs O t ht hr
  have hbi₀ : b i₀ ≠ 0 := hi₀
  set m : Fin r × Fin r → AlgebraicClosure ℚ := fun p => a p.1 * b p.2 - a p.2 * b p.1 with hm
  have hm₀ : m (π, i₀) ≠ 0 := by
    show a π * b i₀ - a i₀ * b π ≠ 0
    rw [haπ, hbπ, one_mul, mul_zero, sub_zero]; exact hbi₀

  set A : Fin r → ℂ := fun i => σ (a i) with hA
  set B : Fin r → ℂ := fun i => σ (b i) with hB
  have hσm : ∀ p : Fin r × Fin r, A p.1 * B p.2 - A p.2 * B p.1 = σ (m p) := fun p => by
    simp only [hA, hB, hm, map_sub, map_mul]
  have hSA1 : 1 ≤ ⨆ i, ‖A i‖ := by
    have h1 : ‖A π‖ = 1 := by simp only [hA, haπ, map_one, norm_one]
    rw [← h1]
    exact le_ciSup (f := fun i => ‖A i‖) (Set.finite_range _).bddAbove π
  have hSA : (⨆ i, ‖A i‖) ≠ 0 := by linarith
  have hAB : (⨆ p : Fin r × Fin r, ‖A p.1 * B p.2 - A p.2 * B p.1‖) ≠ 0 := by
    rw [SeqLimit.ciSup_norm_ne_zero_iff]
    exact ⟨(π, i₀), by rw [hσm]; exact (map_ne_zero σ).2 hm₀⟩

  set z : modularFunctionFieldBar N := u * ((s π)⁻¹) ^ k * (t⁻¹) ^ e with hz
  have hz0 : z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hu (pow_ne_zero _ (inv_ne_zero (hs0 π)))) (pow_ne_zero _ (inv_ne_zero ht0))
  have hzord : O.ord z = 0 := by
    show O.ord (u * ((s π)⁻¹) ^ k * (t⁻¹) ^ e) = 0
    rw [O.ord_mul (mul_ne_zero hu (pow_ne_zero _ (inv_ne_zero (hs0 π)))) (pow_ne_zero _ (inv_ne_zero ht0)),
      O.ord_mul hu (pow_ne_zero _ (inv_ne_zero (hs0 π))), ← zpow_natCast ((s π)⁻¹) k, O.ord_zpow, O.ord_inv, hπord,
      ← zpow_natCast (t⁻¹) e, O.ord_zpow, O.ord_inv, ht]
    linarith
  have hzO : z ∈ O.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg O hz0 hzord.ge
  have htO : t ∈ O.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg O ht0 (by rw [ht]; norm_num)
  have htO0 : O.evalAt t = 0 := SeqLocal.evalAt_eq_zero_of_ord_pos O htO (by rw [ht]; norm_num)
  set Y : Finset (modularFunctionFieldBar N) :=
    insert t (insert z (Finset.univ.image x ∪ Finset.univ.image y)) with hYdef
  have hY : ∀ w ∈ Y, w ∈ O.toValuationSubring := by
    intro w hw
    simp only [hYdef, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hw
    rcases hw with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact htO
    · exact hzO
    · exact hxO i
    · exact hyO i
  obtain ⟨v, hvS, hvO, hvY⟩ : ∃ v : ℕ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ O) ∧
      ∀ y ∈ Y, (∀ n, y ∈ (v n).toValuationSubring) ∧ (y ≠ 0 → ∀ n, (v n).evalAt y ≠ 0) ∧
        Filter.Tendsto (fun n => σ ((v n).evalAt y)) Filter.atTop (nhds (σ (O.evalAt y))) := by
    rcases hv₀ with hinf | hj
    · rw [hinf] at hY ⊢
      exact ModularCurve.exists_seq_place_tendsto_evalAt_cuspInftyBar N σ S Y hY
    · exact ModularCurve.exists_seq_place_tendsto_evalAt N O hj σ S Y hY
  have htY : t ∈ Y := by simp [hYdef]
  have hzY : z ∈ Y := by simp [hYdef]
  have hxY : ∀ i, x i ∈ Y := fun i => by
    simp only [hYdef, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))
  have hyY : ∀ i, y i ∈ Y := fun i => by
    simp only [hYdef, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))
  have htv : ∀ n, t ∈ (v n).toValuationSubring := (hvY t htY).1
  have htv0 : ∀ n, (v n).evalAt t ≠ 0 := (hvY t htY).2.1 ht0
  have htlim := (hvY t htY).2.2
  have hzv : ∀ n, z ∈ (v n).toValuationSubring := (hvY z hzY).1
  have hzv0 : ∀ n, (v n).evalAt z ≠ 0 := (hvY z hzY).2.1 hz0
  have hzlim := (hvY z hzY).2.2
  have hxv : ∀ i n, x i ∈ (v n).toValuationSubring := fun i => (hvY (x i) (hxY i)).1
  have hxv0 : ∀ i n, (v n).evalAt (x i) ≠ 0 := fun i => (hvY (x i) (hxY i)).2.1 (hx0 i)
  have hxlim := fun i => (hvY (x i) (hxY i)).2.2
  have hylim := fun i => (hvY (y i) (hyY i)).2.2

  set X : ℕ → Fin r → ℂ := fun n i => σ ((v n).evalAt (x i)) with hX
  set T : ℕ → ℂ := fun n => σ ((v n).evalAt t) with hT
  set C : ℕ → ℂ := fun n => σ ((v n).evalAt z) * T n ^ e with hC
  have hT0 : ∀ n, T n ≠ 0 := fun n => (map_ne_zero σ).2 (htv0 n)
  have hTlim : Tendsto T atTop (𝓝 0) := by
    have := htlim
    rw [htO0, map_zero] at this
    exact this
  have hXA : ∀ i, Tendsto (fun n => X n i) atTop (𝓝 (A i)) := fun i => hxlim i
  have htord : ∀ n, (v n).ord t = 0 := fun n => SeqLocal.ord_eq_zero_of_evalAt_ne_zero (v n) (htv n) (htv0 n)
  have hXq : ∀ i n, (X n i - A i) / T n = σ ((v n).evalAt (y i)) := by
    intro i n
    have htinv : t⁻¹ ∈ (v n).toValuationSubring := by
      refine AlgebraicCurve.Place.mem_of_ord_nonneg _ (inv_ne_zero ht0) ?_
      rw [(v n).ord_inv, htord n, neg_zero]
    have e1 : (v n).evalAt (y i) = ((v n).evalAt (x i) - a i) * ((v n).evalAt t)⁻¹ := by
      show (v n).evalAt ((x i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a i)) * t⁻¹) = _
      rw [AlgebraicCurve.Place.evalAt_mul _ (hrat _) (sub_mem (hxv i n) ((v n).algebraMap_mem' _)) htinv,
        SeqLocal.evalAt_sub _ (hrat _) (hxv i n) ((v n).algebraMap_mem' _), AlgebraicCurve.Place.evalAt_algebraMap,
        AlgebraicCurve.Place.evalAt_inv _ (hrat _) ht0 (htord n)]
    rw [e1, map_mul, map_sub, map_inv₀, div_eq_mul_inv]
  have hXlim : ∀ i, Tendsto (fun n => (X n i - A i) / T n) atTop (𝓝 (B i)) := fun i => by
    simp only [hXq]; exact hylim i
  have hClim : Tendsto (fun n => C n / T n ^ e) atTop (𝓝 (σ (O.evalAt z))) := by
    have : ∀ n, C n / T n ^ e = σ ((v n).evalAt z) := fun n => by
      show σ ((v n).evalAt z) * T n ^ e / T n ^ e = _
      rw [mul_div_assoc, div_self (pow_ne_zero _ (hT0 n)), mul_one]
    simp only [this]; exact hzlim
  have hρ : σ (O.evalAt z) ≠ 0 := (map_ne_zero σ).2 (AlgebraicCurve.Place.evalAt_ne_zero O (hrat O) hz0 hzord)
  have hL3 := SeqLimit.tendsto_limitAlgebra (k := k) (e := e) hXlim hClim hρ hTlim hT0 hSA hAB
  have hL3b := SeqLimit.eventually_minors_ne_zero hXlim hT0 hAB
  have hreg : regVal s O t k e u = O.evalAt z := by
    simp only [regVal, dif_pos hr]
    rw [hz, hπ]

  have hpiv : ∀ n, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (∀ i, evalVec s (v n) i = c * (v n).evalAt (x i)) ∧
      secVal s (v n) k u = (v n).evalAt z * (v n).evalAt t ^ e * c ^ k := by
    intro n
    have hordj : ∀ j, (v n).ord (s j) = (v n).ord (s π) := fun j => by
      have h1 := SeqLocal.ord_eq_zero_of_evalAt_ne_zero (v n) (hxv j n) (hxv0 j n)
      change (v n).ord (s j * (s π)⁻¹) = 0 at h1
      rw [(v n).ord_mul (hs0 j) (inv_ne_zero (hs0 π)), (v n).ord_inv] at h1
      omega
    set p := pivotIndex s (v n) hr with hp
    set w : modularFunctionFieldBar N := s π * (s p)⁻¹ with hw
    have hw0 : w ≠ 0 := mul_ne_zero (hs0 π) (inv_ne_zero (hs0 p))
    have hword : (v n).ord w = 0 := by
      show (v n).ord (s π * (s p)⁻¹) = 0
      rw [(v n).ord_mul (hs0 π) (inv_ne_zero (hs0 p)), (v n).ord_inv, hordj p]; ring
    have hwv : w ∈ (v n).toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg _ hw0 hword.ge
    refine ⟨(v n).evalAt w, AlgebraicCurve.Place.evalAt_ne_zero _ (hrat _) hw0 hword, fun i => ?_, ?_⟩
    · rw [hev, mul_comm ((v n).evalAt w)]
      have : s i * (s p)⁻¹ = x i * w := by
        show s i * (s p)⁻¹ = s i * (s π)⁻¹ * (s π * (s p)⁻¹)
        field_simp [hs0 π]
      rw [this, AlgebraicCurve.Place.evalAt_mul _ (hrat _) (hxv i n) hwv]
    · simp only [secVal, dif_pos hr]
      have e1 : (t⁻¹) ^ e * t ^ e = 1 := by rw [← mul_pow, inv_mul_cancel₀ ht0, one_pow]
      have e2 : ((s π)⁻¹) ^ k * (s π) ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ (hs0 π), one_pow]
      have : u * ((s p)⁻¹) ^ k = z * t ^ e * w ^ k := by
        rw [hz, hw, mul_pow]
        calc u * ((s p)⁻¹) ^ k = u * (((s π)⁻¹) ^ k * (s π) ^ k) * ((t⁻¹) ^ e * t ^ e) * ((s p)⁻¹) ^ k := by
              rw [e1, e2, mul_one, mul_one]
          _ = _ := by ring
      rw [this, AlgebraicCurve.Place.evalAt_mul _ (hrat _) (mul_mem (hzv n) (pow_mem (htv n) e)) (pow_mem hwv k),
        AlgebraicCurve.Place.evalAt_mul _ (hrat _) (hzv n) (pow_mem (htv n) e),
        SeqLocal.evalAt_pow _ (hrat _) (htv n), SeqLocal.evalAt_pow _ (hrat _) hwv]
  choose c hc0 hcev hcsec using hpiv
  have hXπ : ∀ n, X n π = 1 := fun n => by
    show σ ((v n).evalAt (x π)) = 1
    rw [hxπ, AlgebraicCurve.Place.evalAt_one, map_one]
  have hSX : ∀ n, (⨆ i, ‖X n i‖) ≠ 0 := fun n => by
    rw [SeqLimit.ciSup_norm_ne_zero_iff]; exact ⟨π, by rw [hXπ]; exact one_ne_zero⟩
  have hvecn : ∀ n, (fun i => σ (evalVec s (v n) i)) = σ (c n) • X n := fun n => by
    funext i; simp only [hcev, map_mul, Pi.smul_apply, smul_eq_mul, hX]
  refine ⟨v, hvS, hvO, ?_, ?_⟩
  ·
    intro w hwS hwO
    set W : Fin r → ℂ := fun i => σ (evalVec s w i) with hW
    have hAW : (⨆ p : Fin r × Fin r, ‖A p.1 * W p.2 - A p.2 * W p.1‖) ≠ 0 := by
      rw [SeqLimit.ciSup_norm_ne_zero_iff]
      have hch := ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs O w (Ne.symm hwO)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hch
      refine ⟨p, ?_⟩
      have : A p.1 * W p.2 - A p.2 * W p.1 = σ (chordVec s O w p) := by
        simp only [hA, hW, chordVec, map_sub, map_mul, haO]
      rw [this]; exact (map_ne_zero σ).2 hp
    have hlim : Tendsto (fun n => SeqLimit.cprox (X n) W) atTop (𝓝 (SeqLimit.cprox A W)) :=
      SeqLimit.tendsto_cprox hXA hSA hAW
    have hMWlim : Tendsto (fun n => ⨆ p : Fin r × Fin r, ‖X n p.1 * W p.2 - X n p.2 * W p.1‖) atTop
        (𝓝 (⨆ p : Fin r × Fin r, ‖A p.1 * W p.2 - A p.2 * W p.1‖)) := by
      refine SeqLimit.tendsto_ciSup (u := fun n (p : Fin r × Fin r) => ‖X n p.1 * W p.2 - X n p.2 * W p.1‖) fun p => ?_
      exact (((hXA p.1).mul (tendsto_const_nhds (x := W p.2))).sub ((hXA p.2).mul (tendsto_const_nhds (x := W p.1)))).norm
    have hMW : ∀ᶠ n in atTop, (⨆ p : Fin r × Fin r, ‖X n p.1 * W p.2 - X n p.2 * W p.1‖) ≠ 0 := hMWlim.eventually_ne hAW
    have hev' : ∀ᶠ n in atTop, SeqLimit.cprox (X n) W = prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s w) := by
      filter_upwards [hMW] with n hn
      rw [SeqLocal.prox_eq_cprox, hvecn n, SeqLimit.cprox_smul _ ((map_ne_zero σ).2 (hc0 n)) _ _ (hSX n) hn]
    have htarget : prox (fun a => ‖σ a‖) (evalVec s O) (evalVec s w) = SeqLimit.cprox A W := by
      rw [SeqLocal.prox_eq_cprox, haO]
    rw [htarget]
    exact hlim.congr' hev'
  ·
    have hCn0 : ∀ n, C n ≠ 0 := fun n => mul_ne_zero ((map_ne_zero σ).2 (hzv0 n)) (pow_ne_zero _ (hT0 n))
    have hev' : ∀ᶠ n in atTop,
        (k : ℝ) * Real.log (⨆ i, ‖X n i‖) - Real.log ‖C n‖ - (e : ℝ) * SeqLimit.cprox (X n) A
        = (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖
          - (e : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s O) := by
      filter_upwards [hL3b] with n hn
      rw [SeqLocal.prox_eq_cprox, haO]
      have e2 : σ (secVal s (v n) k u) = C n * σ (c n) ^ k := by
        rw [hcsec, map_mul, map_mul, map_pow, map_pow]
      have e3 : (⨆ i, ‖σ (evalVec s (v n) i)‖) = ⨆ i, ‖(σ (c n) • X n) i‖ := by
        rw [← hvecn n]
      rw [e3, e2, hvecn n]
      exact (SeqLimit.pivot_change _ ((map_ne_zero σ).2 (hc0 n)) (X n) A (C n) (hCn0 n) k e (hSX n) hn).symm

    have hy_id : ∀ p : Fin r × Fin r,
        σ (regVal s O t 1 1 (evalVec s O p.1 • s p.2 - evalVec s O p.2 • s p.1)) = A p.1 * B p.2 - A p.2 * B p.1 := by
      intro p
      have e1 : (a p.1 • s p.2 - a p.2 • s p.1) * (s π)⁻¹ * t⁻¹
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a p.1) * y p.2
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a p.2) * y p.1 := by
        simp only [hy, hx, Algebra.smul_def]
        ring
      have e2 : regVal s O t 1 1 (evalVec s O p.1 • s p.2 - evalVec s O p.2 • s p.1) = a p.1 * b p.2 - a p.2 * b p.1 := by
        simp only [regVal, dif_pos hr, pow_one, haO, hb]
        rw [← hπ, e1, SeqLocal.evalAt_sub O (hrat O) (mul_mem (O.algebraMap_mem' _) (hyO _)) (mul_mem (O.algebraMap_mem' _) (hyO _)),
          AlgebraicCurve.Place.evalAt_mul O (hrat O) (O.algebraMap_mem' _) (hyO _),
          AlgebraicCurve.Place.evalAt_mul O (hrat O) (O.algebraMap_mem' _) (hyO _),
          AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap]
      simp only [hA, hB, e2, map_sub, map_mul]
    have htarget : ((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s O i)‖)
          + (e : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (regVal s O t 1 1 (evalVec s O p.1 • s p.2 - evalVec s O p.2 • s p.1))‖)
          - Real.log ‖σ (regVal s O t k e u)‖
        = (k : ℝ) * Real.log (⨆ i, ‖A i‖) - Real.log ‖σ (O.evalAt z)‖
          + (e : ℝ) * (Real.log (⨆ p : Fin r × Fin r, ‖A p.1 * B p.2 - A p.2 * B p.1‖) - 2 * Real.log (⨆ i, ‖A i‖)) := by
      simp only [hy_id]
      rw [hreg, haO]
      ring
    rw [htarget]
    exact hL3.congr' hev'

end S_ModularCurve_JZero_exists_seq_tendsto_place
end P2MW
export P2MW.S_ModularCurve_JZero_exists_seq_tendsto_place (solution)
