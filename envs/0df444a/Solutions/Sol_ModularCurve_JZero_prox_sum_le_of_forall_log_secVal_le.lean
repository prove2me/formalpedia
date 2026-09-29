-- Prove2me | solution 1 for ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f30b2811-9e75-5700-8761-7f300cb3437f

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_ModularCurve_CuspSpace
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_bddAbove_chowLogAt_range
import Theorems.Thm_ModularCurve_JZero_jensen_arch_embedding
import Theorems.Thm_ModularCurve_JZero_prox_sum_chowSide
import Theorems.Thm_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree
import Theorems.Thm_ModularCurve_JZero_sum_toNat_sectionCycle_eq_mul_embDegree
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_Pencil_exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge
import Theorems.Thm_RingHom_mem_range_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_prox_sum_le_of_forall_log_secVal_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open UpperHalfPlane Filter AlgebraicCurve ModularCurve
open scoped Topology MatrixGroups

noncomputable section

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

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem hypSec_facts (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ Za w ∧ (Za w = 0 ↔ ∑ i, evalVec s w i * a i ≠ 0) := by
  classical
  have hr := r_pos N s hs
  have hv := isRational N w
  obtain ⟨hGmem, hGval⟩ := evalAt_sum_smul w hv Finset.univ a
    (fun i => s i * (s (pivotIndex s w hr))⁻¹) (fun i _ => (ratio_mem N s hs w hr i).1)
  have hGval' : w.evalAt (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) = ∑ i, evalVec s w i * a i := by
    rw [hGval]
    exact Finset.sum_congr rfl fun i _ => by rw [(ratio_mem N s hs w hr i).2.2, mul_comm]
  have hfactor : linSec s a = (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) * s (pivotIndex s w hr) := by
    rw [Finset.sum_mul]
    unfold linSec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, inv_mul_cancel_right₀ (s_ne_zero N s hs _)]
  have hG0 : (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) ≠ 0 := by
    intro h0; apply ha; rw [hfactor, h0, zero_mul]
  have hZaw : Za w = w.ord (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) := by
    rw [hZa w, hfactor, w.ord_mul hG0 (s_ne_zero N s hs _), ord_pivot N s hs w hr]; ring
  refine ⟨hZaw ▸ w.ord_nonneg_of_mem hGmem, ?_⟩
  rw [hZaw, ← hGval']
  constructor
  · intro h0; exact w.evalAt_ne_zero hv hG0 h0
  · intro hne
    by_contra hne0
    have hpos : 0 < w.ord (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) :=
      lt_of_le_of_ne (w.ord_nonneg_of_mem hGmem) (Ne.symm hne0)
    apply hne
    rw [← evalAt_zero' w]
    exact w.evalAt_congr hGmem (zero_mem _) (Or.inr (by simpa using hpos))

end L2

namespace PLBALG

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem exists_pinned (s : Fin r → modularFunctionFieldBar N) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) :
    ∃ Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ w, Za w = w.ord (linSec s a) + embDivisor N w := by
  have hcurve := ModularCurve.isCurveOver_modularFunctionFieldBar N
  obtain ⟨D, hD, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ ha
  exact ⟨D + embDivisor N, fun w => by rw [Finsupp.add_apply, hD]⟩

end PLBALG

namespace JPLUSE
open AlgebraicCurve ModularCurve

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem eval_chowForm (s : Fin r → modularFunctionFieldBar N) (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (e : Fin r → AlgebraicClosure ℚ) :
    MvPolynomial.eval e (chowForm s Z) = Z.prod fun w n => (∑ i, evalVec s w i * e i) ^ n.toNat := by
  unfold chowForm
  rw [Finsupp.prod, map_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_pow, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem log_norm_eval_chowForm (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → modularFunctionFieldBar N)
    (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (e : Fin r → AlgebraicClosure ℚ)
    (hne : ∀ w ∈ Z.support, σ (∑ i, evalVec s w i * e i) ≠ 0) :
    σ (MvPolynomial.eval e (chowForm s Z)) ≠ 0 ∧
    Real.log ‖σ (MvPolynomial.eval e (chowForm s Z))‖
      = Z.sum fun w n => (n.toNat : ℝ) * Real.log ‖σ (∑ i, evalVec s w i * e i)‖ := by
  rw [eval_chowForm, Finsupp.prod, map_prod]
  constructor
  · rw [Finset.prod_ne_zero_iff]
    intro w hw
    rw [map_pow]
    exact pow_ne_zero _ (hne w hw)
  · rw [norm_prod, Real.log_prod (fun w hw => by rw [map_pow, norm_pow]; exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hne w hw))),
      Finsupp.sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [map_pow, norm_pow, Real.log_pow]

set_option maxHeartbeats 8000000 in

theorem prox_sum_le (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ S : ℝ, (∀ y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B y = 0 →
          Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖) ≤ S) →
        ((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) *
            prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w))
          ≤ (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
              - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ + S + c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
            ≤ (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - Real.log ‖σ (secVal s v k u)‖ + S + c * k := by
  classical
  obtain ⟨cE, hE⟩ := ModularCurve.JZero.jensen_arch_embedding N s hs t ht
  obtain ⟨c₃, h₃⟩ := ModularCurve.JZero.prox_sum_chowSide N s hs
  set d : ℕ := embDegree N with hd
  set CA : ℝ := ((r + 1 : ℕ) : ℝ) * Real.log 2 + 1 with hCA
  have hCA0 : 0 ≤ CA := by rw [hCA]; positivity
  refine ⟨CA * d + c₃ + 2 * cE, fun σ k u hu huL B hB S hS => ?_⟩
  have hr := L2.r_pos N s hs
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨m, hEc, hEv⟩ := hE σ k u hu huL B hB
  obtain ⟨h₃c, h₃v⟩ := h₃ σ k u hu huL B hB
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k

  have hBnn : ∀ w, 0 ≤ B w := fun w => by
    rw [hB w]
    have := L2.neg_le_ord_of_mem _ huL hu w
    linarith

  have hpiv : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      evalVec s w (pivotIndex s w hr) = 1 := fun w => evalVec_pivotIndex s w hr (hs0 _)

  set v' : Fin (r + 1) → ℂ := Fin.snoc (fun _ : Fin r => (0 : ℂ)) 1 with hv'
  set w' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin (r + 1) → ℂ :=
    fun w => Fin.snoc (fun i : Fin r => σ (evalVec s w i)) 0 with hw'
  have hv'last : v' (Fin.last r) = 1 := by simp [hv']
  have hv'cs : ∀ i : Fin r, v' (Fin.castSucc i) = 0 := fun i => by simp [hv']
  have hw'last : ∀ w, w' w (Fin.last r) = 0 := fun w => by simp [hw']
  have hw'cs : ∀ w (i : Fin r), w' w (Fin.castSucc i) = σ (evalVec s w i) := fun w i => by simp [hw']
  have hi₀ : ∀ j, ‖v' j‖ ≤ ‖v' (Fin.last r)‖ := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact le_rfl
    · rw [hv'cs, hv'last]; simp
  have hminor : ∀ w (i : Fin r), v' (Fin.last r) * w' w (Fin.castSucc i) - v' (Fin.castSucc i) * w' w (Fin.last r)
      = σ (evalVec s w i) := by
    intro w i; rw [hv'last, hv'cs, hw'cs, hw'last]; ring
  have hw : ∀ w ∈ B.support, ∃ p : Fin (r + 1) × Fin (r + 1), v' p.1 * w' w p.2 - v' p.2 * w' w p.1 ≠ 0 := by
    intro w _
    refine ⟨(Fin.last r, Fin.castSucc (pivotIndex s w hr)), ?_⟩
    rw [hminor, hpiv, map_one]; exact one_ne_zero
  obtain ⟨z, hzroot, hNE, hSUM⟩ :=
    Pencil.exists_rootOfUnity_torus_covector_ne_zero_sum_log_ge v' hi₀ B.support w' (fun w => (B w).toNat) hw

  have hcomb : ∀ w, (∑ j, z j * (v' (Fin.last r) * w' w j - v' j * w' w (Fin.last r)))
      = ∑ i : Fin r, z (Fin.castSucc i) * σ (evalVec s w i) := by
    intro w
    rw [Fin.sum_univ_castSucc]
    simp only [hminor, hv'last, hw'last, hw'cs, hv'cs, mul_zero, zero_mul, sub_zero, add_zero, one_mul]

  have hrange : ∀ i : Fin r, z (Fin.castSucc i) ∈ σ.range := by
    intro i
    obtain ⟨mi, hmi, hzi⟩ := hzroot (Fin.castSucc i)
    exact RingHom.mem_range_of_pow_eq_one σ hmi hzi
  choose e he using fun i => RingHom.mem_range.mp (hrange i)
  have hnorm1 : ∀ i, ‖σ (e i)‖ = 1 := by
    intro i
    obtain ⟨mi, hmi, hzi⟩ := hzroot (Fin.castSucc i)
    rw [he i]; exact Complex.norm_eq_one_of_pow_eq_one hzi hmi.ne'
  have he0 : e ≠ 0 := by
    intro h0
    have := hnorm1 ⟨0, hr⟩
    rw [h0, Pi.zero_apply, map_zero, norm_zero] at this
    exact zero_ne_one this
  have hsup1 : (⨆ i, ‖σ (e i)‖) = 1 := by simp only [hnorm1, ciSup_const]
  have hcombσ : ∀ w, (∑ i : Fin r, z (Fin.castSucc i) * σ (evalVec s w i)) = σ (∑ i, evalVec s w i * e i) := by
    intro w
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, he i, mul_comm]

  have hle0 : linSec s e ≠ 0 := by
    intro h0
    apply he0
    funext i
    have hli := Fintype.linearIndependent_iff.mp hs.1 e (by simpa [linSec] using h0) i
    exact hli
  obtain ⟨Ze, hZe⟩ := PLBALG.exists_pinned s e hle0
  have hdeg : (Ze.sum fun _ n => n.toNat) = d :=
    ModularCurve.JZero.sum_toNat_hyperplaneSection_eq_embDegree N s hs e hle0 Ze hZe
  have hdpos : 0 < d := by rw [hd]; unfold embDegree; omega
  obtain ⟨v₁, hv₁supp, hv₁⟩ : ∃ v₁ ∈ Ze.support, (Ze v₁).toNat ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [← Finsupp.sum, hdeg]; exact hdpos.ne'
  have hZpos : 0 < Ze v₁ := by
    by_contra hle; push_neg at hle
    exact hv₁ (Int.toNat_eq_zero.mpr hle)
  have hORTH : ∑ i, evalVec s v₁ i * e i = 0 := by
    have hf := (L2.hypSec_facts N s hs e hle0 Ze hZe v₁).2
    by_contra hne
    exact hZpos.ne' (hf.mpr hne)
  have hBv₁ : B v₁ = 0 := by
    by_contra hB0
    have := hNE v₁ (Finsupp.mem_support_iff.mpr hB0)
    rw [hcomb, hcombσ, hORTH, map_zero] at this
    exact this rfl

  set ν : AlgebraicClosure ℚ → ℝ := fun a => ‖σ a‖ with hν
  have hne : ∀ w ∈ B.support, σ (∑ i, evalVec s w i * e i) ≠ 0 := fun w hw => by
    rw [← hcombσ, ← hcomb]; exact hNE w hw
  obtain ⟨hq0, hlogq⟩ := log_norm_eval_chowForm σ s B e hne
  set q : ℝ := ‖σ (MvPolynomial.eval e (chowForm s B))‖ / (⨆ i, ‖σ (e i)‖) ^ (B.sum fun _ n => n.toNat) with hq
  have hq_eq : q = ‖σ (MvPolynomial.eval e (chowForm s B))‖ := by rw [hq, hsup1, one_pow, div_one]
  have hqpos : 0 < q := by rw [hq_eq]; exact norm_pos_iff.mpr hq0

  have hchow : Real.log q ≤ chowLogAt ν s B v₁ := by
    unfold chowLogAt
    apply Real.log_le_log hqpos
    have hbdd := AlgebraicCurve.bddAbove_chowLogAt_range σ s B v₁
    exact le_ciSup hbdd ⟨e, hORTH, he0⟩

  have hsupM : ∀ w, Real.log (⨆ i, ‖σ (evalVec s w i)‖)
      ≤ Real.log (⨆ p : Fin (r + 1) × Fin (r + 1), ‖v' p.1 * w' w p.2 - v' p.2 * w' w p.1‖) := by
    intro w
    have hpos : 0 < ⨆ i, ‖σ (evalVec s w i)‖ := by
      refine lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ?_
      have h1 : ‖σ (evalVec s w (pivotIndex s w hr))‖ = 1 := by rw [hpiv, map_one, norm_one]
      rw [← h1]
      exact le_ciSup (Set.finite_range fun i : Fin r => ‖σ (evalVec s w i)‖).bddAbove (pivotIndex s w hr)
    apply Real.log_le_log hpos
    refine ciSup_le fun i => ?_
    have := le_ciSup (Set.finite_range fun p : Fin (r + 1) × Fin (r + 1) => ‖v' p.1 * w' w p.2 - v' p.2 * w' w p.1‖).bddAbove
      (Fin.last r, Fin.castSucc i)
    rwa [hminor] at this

  have hsumB : (B.sum fun _ n => n.toNat) = k * d :=
    ModularCurve.JZero.sum_toNat_sectionCycle_eq_mul_embDegree N k u hu huL B hB
  have hsumBR : (∑ w ∈ B.support, ((B w).toNat : ℝ)) = k * d := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hsumB
    simpa [Finsupp.sum] using this

  have hT1 : (B.sum fun w n => (n : ℝ) * Real.log (⨆ i, ν (evalVec s w i)))
      = ∑ w ∈ B.support, ((B w).toNat : ℝ) * Real.log (⨆ i, ‖σ (evalVec s w i)‖) := by
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have : ((B w : ℤ) : ℝ) = ((B w).toNat : ℝ) := by
      have h := Int.toNat_of_nonneg (hBnn w)
      exact_mod_cast h.symm
    rw [this]
  have hside : chowSide ν s B v₁ ≤ CA * (k * d) := by
    unfold chowSide
    rw [hT1]
    have h1 : ∑ w ∈ B.support, ((B w).toNat : ℝ) * Real.log (⨆ i, ‖σ (evalVec s w i)‖)
        ≤ ∑ w ∈ B.support, ((B w).toNat : ℝ) *
            Real.log (⨆ p : Fin (r + 1) × Fin (r + 1), ‖v' p.1 * w' w p.2 - v' p.2 * w' w p.1‖) :=
      Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hsupM w) (Nat.cast_nonneg _)
    have h2 : ∑ w ∈ B.support, ((B w).toNat : ℝ) * Real.log ‖∑ j, z j * (v' (Fin.last r) * w' w j - v' j * w' w (Fin.last r))‖
        = Real.log q := by
      rw [hq_eq, hlogq, Finsupp.sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hcomb, hcombσ]
    have h3 : ((r : ℝ) + 1) * Real.log 2 + 1 = CA := by rw [hCA]; push_cast; ring
    have hS' := hSUM
    rw [h2, hsumBR] at hS'

    have h4 : ((((r + 1 : ℕ)) : ℝ) * Real.log 2 + 1) = CA := by rw [hCA]
    push_cast at hS' h4
    nlinarith [h1, hchow, hS', h4]

  have hm : -m ≤ (CA * d + c₃ + cE) * k + S := by
    have a1 := (abs_sub_le_iff.mp (h₃v v₁ hBv₁)).1
    have a2 := (abs_sub_le_iff.mp (hEv v₁ hBv₁)).2
    have a3 := hS v₁ hBv₁
    nlinarith [a1, a2, a3, hside]
  refine ⟨?_, fun v hv => ?_⟩
  · have b1 := (abs_sub_le_iff.mp hEc).1
    nlinarith [b1, hm]
  · have b1 := (abs_sub_le_iff.mp (hEv v hv)).1
    nlinarith [b1, hm]

end JPLUSE

end

open AlgebraicCurve ModularCurve in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ S : ℝ, (∀ y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B y = 0 →
          Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖) ≤ S) →
        ((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) *
            prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w))
          ≤ (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
              - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ + S + c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
            ≤ (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - Real.log ‖σ (secVal s v k u)‖ + S + c * k :=
  JPLUSE.prox_sum_le s hs t ht

end S_ModularCurve_JZero_prox_sum_le_of_forall_log_secVal_le
end P2MW
export P2MW.S_ModularCurve_JZero_prox_sum_le_of_forall_log_secVal_le (solution)
