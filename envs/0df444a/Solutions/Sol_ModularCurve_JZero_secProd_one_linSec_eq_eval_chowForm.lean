-- Prove2me | solution 1 for ModularCurve.JZero.secProd_one_linSec_eq_eval_chowForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a18141cd-4aff-5cf9-a0dc-d26331c98c45

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_secProd_one_linSec_eq_eval_chowForm
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

open AlgebraicCurve ModularCurve

namespace L2

theorem isRational (N : ℕ) [NeZero N] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : w.IsRational :=
  (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField w).1
    (ModularCurve.deg_eq_one_modularFunctionFieldBar N w)

theorem evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_zero' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.evalAt (0 : F) = 0 := by
  simpa using v.evalAt_algebraMap (0 : K)

theorem evalAt_sum_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {ι : Type*} (t : Finset ι) (a : ι → K) (g : ι → F) (hg : ∀ i ∈ t, g i ∈ v.toValuationSubring) :
    (∑ i ∈ t, a i • g i) ∈ v.toValuationSubring ∧
    v.evalAt (∑ i ∈ t, a i • g i) = ∑ i ∈ t, a i * v.evalAt (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨by simp, by simp [evalAt_zero']⟩
  | insert j t hj ih =>
    obtain ⟨hmem, hval⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgj : g j ∈ v.toValuationSubring := hg j (Finset.mem_insert_self _ _)
    have hsm : a j • g j ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) hgj
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    refine ⟨add_mem hsm hmem, ?_⟩
    rw [evalAt_add' v hv hsm hmem, hval, Algebra.smul_def, v.evalAt_mul hv (v.algebraMap_mem' _) hgj,
      v.evalAt_algebraMap]

theorem neg_le_ord_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) {f : F}
    (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0) (w : Place K F) : -D w ≤ w.ord f := by
  have hval : w.adicValuation f ≤ WithZero.exp (D w) := hf w
  have hlog := (WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf0)).2 hval
  simp only [AlgebraicCurve.Place.ord]
  linarith

theorem r_pos (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h
  · exfalso
    subst h0
    have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
      rw [mem_riemannRochSpace_iff]
      intro w
      right
      rw [w.ord_one, neg_nonpos]
      classical
      simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> simp
    rw [← hs.2] at h1
    have : Set.range s = ∅ := Set.range_eq_empty s
    rw [this, Submodule.span_empty, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

theorem s_ne_zero (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

theorem s_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) : s i ∈ riemannRochSpace (embDivisor N) := by
  rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem ord_pivot (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) : w.ord (s (pivotIndex s w hr)) = -embDivisor N w := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact Finite.exists_min fun i => w.ord (s i)
  have hpiv : ∀ j, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    unfold pivotIndex
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  obtain ⟨i₀, hi₀⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs w
  refine le_antisymm (by linarith [hpiv i₀]) ?_
  exact neg_le_ord_of_mem _ (s_mem N s hs _) (s_ne_zero N s hs _) w

theorem ratio_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) (i : Fin r) :
    s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring ∧
    0 ≤ w.ord (s i * (s (pivotIndex s w hr))⁻¹) ∧
    w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) = evalVec s w i := by
  have hne : s i * (s (pivotIndex s w hr))⁻¹ ≠ 0 :=
    mul_ne_zero (s_ne_zero N s hs i) (inv_ne_zero (s_ne_zero N s hs _))
  have hord : 0 ≤ w.ord (s i * (s (pivotIndex s w hr))⁻¹) := by
    rw [w.ord_mul (s_ne_zero N s hs i) (inv_ne_zero (s_ne_zero N s hs _)), w.ord_inv, ord_pivot N s hs w hr]
    have := neg_le_ord_of_mem _ (s_mem N s hs i) (s_ne_zero N s hs i) w
    linarith
  refine ⟨w.mem_of_ord_nonneg hne hord, hord, ?_⟩
  simp only [evalVec, dif_pos hr]

end L2

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (e : Fin r → AlgebraicClosure ℚ) (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    secProd s 1 (linSec s e) Z = MvPolynomial.eval e (chowForm s Z) := by
  classical
  have hr := L2.r_pos N s hs
  rw [eval_chowForm]
  unfold secProd
  refine Finsupp.prod_congr fun w _ => ?_
  congr 1
  have hv := L2.isRational N w
  obtain ⟨hGmem, hGval⟩ := L2.evalAt_sum_smul w hv Finset.univ e
    (fun i => s i * (s (pivotIndex s w hr))⁻¹) (fun i _ => (L2.ratio_mem N s hs w hr i).1)
  have hfactor : linSec s e * ((s (pivotIndex s w hr))⁻¹) ^ 1 = ∑ i, e i • (s i * (s (pivotIndex s w hr))⁻¹) := by
    rw [pow_one]
    unfold linSec
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc]
  simp only [secVal, dif_pos hr]
  rw [hfactor, hGval]
  exact Finset.sum_congr rfl fun i _ => by rw [(L2.ratio_mem N s hs w hr i).2.2, mul_comm]

end S_ModularCurve_JZero_secProd_one_linSec_eq_eval_chowForm
end P2MW
export P2MW.S_ModularCurve_JZero_secProd_one_linSec_eq_eval_chowForm (solution)
