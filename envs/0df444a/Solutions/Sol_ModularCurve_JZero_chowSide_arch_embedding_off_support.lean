-- Prove2me | solution 1 for ModularCurve.JZero.chowSide_arch_embedding_off_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/11ee7ffb-2450-5976-9ab3-114822cd1719

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_JZero_pencil_secProd_chowForm_two_sided
import Theorems.Thm_ModularCurve_JZero_sum_toNat_sectionCycle_eq_mul_embDegree
import Theorems.Thm_AlgebraicCurve_bddAbove_chowLogAt_range
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_chordVec_ne_zero_of_ne
import Theorems.Thm_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_chowSide_arch_embedding_off_support
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

open AlgebraicCurve ModularCurve

namespace L2lin

variable {K : Type*} [Field K] {r : ℕ}

def dot (x a : Fin r → K) : K := ∑ i, x i * a i

theorem dot_add (x a b : Fin r → K) : dot x (a + b) = dot x a + dot x b := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_smul (x a : Fin r → K) (t : K) : dot x (t • a) = t * dot x a := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_zero (x : Fin r → K) : dot x 0 = 0 := by simp [dot]

theorem exists_avoid [Infinite K] (xv : Fin r → K) (T : Finset (Fin r → K))
    (hT : ∀ x ∈ T, ∃ e : Fin r → K, dot xv e = 0 ∧ dot x e ≠ 0) :
    ∃ a : Fin r → K, dot xv a = 0 ∧ ∀ x ∈ T, dot x a ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, dot_zero _, by simp⟩
  | insert x T hx ih =>
    obtain ⟨a, hav, haT⟩ := ih (fun y hy => hT y (Finset.mem_insert_of_mem hy))
    obtain ⟨e, hev, hex⟩ := hT x (Finset.mem_insert_self _ _)
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
      (insert (-(dot x a) / dot x e) (T.image fun y => -(dot y a) / dot y e))
    refine ⟨a + t • e, ?_, ?_⟩
    · rw [dot_add, dot_smul, hav, hev, mul_zero, add_zero]
    · intro y hy
      rw [dot_add, dot_smul]
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · intro h0
        apply ht
        rw [Finset.mem_insert]; left
        rw [eq_div_iff hex]; linear_combination h0
      · intro h0
        by_cases hye : dot y e = 0
        · rw [hye, mul_zero, add_zero] at h0; exact haT y hy h0
        · apply ht
          rw [Finset.mem_insert]; right
          rw [Finset.mem_image]
          exact ⟨y, hy, by rw [div_eq_iff hye]; linear_combination -h0⟩

theorem finite_bad (a₀ a' : Fin r → K) (T : Finset (Fin r → K)) (hT : ∀ x ∈ T, dot x a' ≠ 0) :
    Set.Finite {t : K | ∃ x ∈ T, dot x (a₀ + t • a') = 0} := by
  classical
  refine ((T.finite_toSet.image fun x => -(dot x a₀) / dot x a')).subset ?_
  rintro t ⟨x, hx, h0⟩
  refine ⟨x, hx, ?_⟩
  rw [dot_add, dot_smul] at h0
  rw [div_eq_iff (hT x hx)]; linear_combination -h0

theorem finite_eq_zero (a₀ a' : Fin r → K) (ha₀ : a₀ ≠ 0) : Set.Finite {t : K | a₀ + t • a' = 0} := by
  refine Set.Subsingleton.finite ?_
  intro t₁ h₁ t₂ h₂
  simp only [Set.mem_setOf_eq] at h₁ h₂
  by_contra hne
  have h : (t₁ - t₂) • a' = 0 := by
    rw [sub_smul]
    have e1 : t₁ • a' = -a₀ := eq_neg_of_add_eq_zero_right h₁
    have e2 : t₂ • a' = -a₀ := eq_neg_of_add_eq_zero_right h₂
    rw [e1, e2, sub_self]
  rcases smul_eq_zero.1 h with h0 | h0
  · exact hne (sub_eq_zero.1 h0)
  · apply ha₀
    rw [h0, smul_zero, add_zero] at h₁
    exact h₁

end L2lin

namespace L2

noncomputable def I {N : ℕ} [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N)
    (B Zb Zc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (b c : Fin r → AlgebraicClosure ℚ) : ℝ :=
  Real.log ‖σ (MvPolynomial.eval b (chowForm s B))‖
    + k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Zb))‖
    - k * Real.log ‖σ (MvPolynomial.eval b (chowForm s Zc))‖
    - Real.log ‖σ (secProd s k u Zb)‖

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem linSec_zero {N : ℕ} [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) :
    linSec s (0 : Fin r → AlgebraicClosure ℚ) = 0 := by
  unfold linSec
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, Algebra.smul_def, map_zero, zero_mul]

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

theorem hypSec_eq_zero_iff (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Za w = 0 ↔ ∑ i, evalVec s w i * a i ≠ 0 :=
  (hypSec_facts N s hs a ha Za hZa w).2

theorem hypSec_nonneg (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : 0 ≤ Za w :=
  (hypSec_facts N s hs a ha Za hZa w).1

theorem secVal_ne_zero_iff (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (k : ℕ) (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    secVal s w k u ≠ 0 ↔ B w = 0 := by
  classical
  have hr := r_pos N s hs
  have hv := isRational N w
  have hsv : secVal s w k u = w.evalAt (u * ((s (pivotIndex s w hr))⁻¹) ^ k) := by
    simp only [secVal, dif_pos hr]
  have hpk : ((s (pivotIndex s w hr))⁻¹) ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero (s_ne_zero N s hs _))
  have hne : u * ((s (pivotIndex s w hr))⁻¹) ^ k ≠ 0 := mul_ne_zero hu hpk
  have hord : w.ord (u * ((s (pivotIndex s w hr))⁻¹) ^ k) = B w := by
    rw [w.ord_mul hu hpk, ← zpow_natCast, w.ord_zpow, w.ord_inv, ord_pivot N s hs w hr, hB w]
    simp only [Finsupp.smul_apply, smul_eq_mul, neg_neg]
  have hBw : 0 ≤ B w := by
    rw [hB w]
    have := neg_le_ord_of_mem _ huL hu w
    simp only [Finsupp.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have hmem : u * ((s (pivotIndex s w hr))⁻¹) ^ k ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg hne (hord ▸ hBw)
  rw [hsv, ← hord]
  constructor
  · intro h
    by_contra hne0
    have hpos : 0 < w.ord (u * ((s (pivotIndex s w hr))⁻¹) ^ k) :=
      lt_of_le_of_ne (w.ord_nonneg_of_mem hmem) (Ne.symm hne0)
    apply h
    rw [← evalAt_zero' w]
    exact w.evalAt_congr hmem (zero_mem _) (Or.inr (by simpa using hpos))
  · intro h0
    exact w.evalAt_ne_zero hv hne h0

theorem secProd_ne_zero {N : ℕ} [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (k : ℕ) (u : modularFunctionFieldBar N) (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (h : ∀ w, 0 < Z w → secVal s w k u ≠ 0) :
    secProd s k u Z ≠ 0 := by
  classical
  rw [secProd, Finsupp.prod, Finset.prod_ne_zero_iff]
  intro w _
  rcases le_or_gt (Z w) 0 with hle | hlt
  · rw [Int.toNat_of_nonpos hle, pow_zero]; exact one_ne_zero
  · exact pow_ne_zero _ (h w hlt)

theorem secProd_eq_secVal_mul {N : ℕ} [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (k : ℕ) (u : modularFunctionFieldBar N) (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hZ : ∀ w, 0 ≤ Z w) (hv : 1 ≤ Z v) :
    secProd s k u Z = secVal s v k u * secProd s k u (Z - Finsupp.single v (1 : ℤ)) := by
  classical
  unfold secProd
  have hv' : v ∈ Z.support := by
    rw [Finsupp.mem_support_iff]; omega
  rw [← Finsupp.mul_prod_erase Z v _ hv']
  by_cases hZv1 : Z v = 1
  ·
    have he : Z - Finsupp.single v 1 = Finsupp.erase v Z := by
      ext w
      by_cases hw : w = v
      · subst hw; simp [hZv1]
      · simp [Finsupp.erase_ne hw, Finsupp.single_apply, Ne.symm hw]
    rw [he, hZv1]
    simp
  · have hv'' : v ∈ (Z - Finsupp.single v (1 : ℤ)).support := by
      rw [Finsupp.mem_support_iff]; simp; omega
    rw [← Finsupp.mul_prod_erase (Z - Finsupp.single v (1 : ℤ)) v _ hv'']
    have he : Finsupp.erase v (Z - Finsupp.single v (1 : ℤ)) = Finsupp.erase v Z := by
      ext w
      by_cases hw : w = v
      · subst hw; simp
      · simp [Finsupp.erase_ne hw, Finsupp.single_apply, Ne.symm hw]
    rw [he, ← mul_assoc]
    congr 1
    have : (Z v).toNat = ((Z - Finsupp.single v (1 : ℤ)) v).toNat + 1 := by
      simp; omega
    rw [this, pow_succ]
    ring

theorem eval_chowForm_ne_zero_iff {N : ℕ} [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : Fin r → AlgebraicClosure ℚ) :
    MvPolynomial.eval a (chowForm s Z) ≠ 0 ↔ ∀ w, Z w ≤ 0 ∨ ∑ i, evalVec s w i * a i ≠ 0 := by
  classical
  rw [eval_chowForm, Finsupp.prod, Finset.prod_ne_zero_iff]
  constructor
  · intro h w
    by_cases hw : w ∈ Z.support
    · have := h w hw
      rcases Nat.eq_zero_or_pos (Z w).toNat with h0 | hpos
      · left; exact Int.toNat_eq_zero.1 h0
      · right; exact fun h' => this (by rw [h', zero_pow hpos.ne'])
    · left; rw [Finsupp.notMem_support_iff.1 hw]
  · intro h w hw
    rcases h w with hle | hne
    · rw [Int.toNat_of_nonpos hle, pow_zero]; exact one_ne_zero
    · exact pow_ne_zero _ hne

theorem log_chowForm_eq (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (hCRB : ChowReciprocity s (embDivisor N) k u B)
    (c : Fin r → AlgebraicClosure ℚ) (Zc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hc : linSec s c ≠ 0)
    (hZc : ∀ w, Zc w = w.ord (linSec s c) + embDivisor N w) (hBZc : ∀ w, B w = 0 ∨ Zc w = 0)
    (b : Fin r → AlgebraicClosure ℚ) (Zb : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hb : linSec s b ≠ 0)
    (hZb : ∀ w, Zb w = w.ord (linSec s b) + embDivisor N w)
    (hZbB : ∀ w, Zb w = 0 ∨ B w = 0) (hZbZc : ∀ w, Zb w = 0 ∨ Zc w = 0)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hBv : B v = 0) (hZcv : Zc v = 0)
    (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (ha : linSec s a ≠ 0)
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w)
    (hav : ∑ i, evalVec s v i * a i = 0) (haZc : ∀ w, Za w = 0 ∨ Zc w = 0)
    (haB : ∀ w, w ≠ v → Za w = 0 ∨ B w = 0) :
    MvPolynomial.eval a (chowForm s B) ≠ 0 ∧ secVal s v k u ≠ 0 ∧
    Real.log ‖σ (MvPolynomial.eval a (chowForm s B))‖
      = I s σ k u B Zb Zc b c + Real.log ‖σ (secVal s v k u)‖
        + (Real.log ‖σ (secProd s k u (Za - Finsupp.single v (1 : ℤ)))‖
            + k * Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
            - k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖) := by
  classical
  have Sa := fun w => hypSec_facts N s hs a ha Za hZa w
  have Sb := fun w => hypSec_facts N s hs b hb Zb hZb w
  have Sc := fun w => hypSec_facts N s hs c hc Zc hZc w
  have SV := fun w => secVal_ne_zero_iff N s hs k u hu huL B hB w

  have hGP : ∀ w, (Za w = 0 ∧ Zb w = 0) ∨ (B w = 0 ∧ Zc w = 0) := by
    intro w
    by_cases hZaw : Za w = 0
    · by_cases hZbw : Zb w = 0
      · exact Or.inl ⟨hZaw, hZbw⟩
      · exact Or.inr ⟨(hZbB w).resolve_left hZbw, (hZbZc w).resolve_left hZbw⟩
    · right
      by_cases hwv : w = v
      · subst hwv; exact ⟨hBv, hZcv⟩
      · exact ⟨(haB w hwv).resolve_left hZaw, (haZc w).resolve_left hZaw⟩
  have hCR := hCRB a b c Za Zb Zc ha hb hc hZa hZb hZc hGP

  have nzF : ∀ (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (e : Fin r → AlgebraicClosure ℚ),
      (∀ w, 0 < Z w → ∑ i, evalVec s w i * e i ≠ 0) → MvPolynomial.eval e (chowForm s Z) ≠ 0 :=
    fun Z e h => (eval_chowForm_ne_zero_iff s Z e).2 fun w => (le_or_gt (Z w) 0).imp_right (h w)
  have hBv' : ∀ w, 0 < B w → w ≠ v := fun w hw hwv => by subst hwv; rw [hBv] at hw; exact lt_irrefl _ hw
  have hFBa : MvPolynomial.eval a (chowForm s B) ≠ 0 :=
    nzF B a fun w hw => (Sa w).2.1 ((haB w (hBv' w hw)).resolve_right hw.ne')
  have hFZcb : MvPolynomial.eval b (chowForm s Zc) ≠ 0 :=
    nzF Zc b fun w hw => (Sb w).2.1 ((hZbZc w).resolve_right hw.ne')
  have hFZac : MvPolynomial.eval c (chowForm s Za) ≠ 0 :=
    nzF Za c fun w hw => (Sc w).2.1 ((haZc w).resolve_left hw.ne')
  have hFBb : MvPolynomial.eval b (chowForm s B) ≠ 0 :=
    nzF B b fun w hw => (Sb w).2.1 ((hZbB w).resolve_right hw.ne')
  have hFZca : MvPolynomial.eval a (chowForm s Zc) ≠ 0 :=
    nzF Zc a fun w hw => (Sa w).2.1 ((haZc w).resolve_right hw.ne')
  have hFZbc : MvPolynomial.eval c (chowForm s Zb) ≠ 0 :=
    nzF Zb c fun w hw => (Sc w).2.1 ((hZbZc w).resolve_left hw.ne')
  have hUZb : secProd s k u Zb ≠ 0 :=
    secProd_ne_zero s k u Zb fun w hw => (SV w).2 ((hZbB w).resolve_left hw.ne')
  have hUZa : secProd s k u Za ≠ 0 :=
    secProd_ne_zero s k u Za fun w hw => (SV w).2 (by
      by_cases hwv : w = v
      · subst hwv; exact hBv
      · exact (haB w hwv).resolve_left hw.ne')
  have hsv : secVal s v k u ≠ 0 := (SV v).2 hBv

  have hZav : 1 ≤ Za v := by
    have h0 : Za v ≠ 0 := fun h => ((Sa v).2.1 h) hav
    have := (Sa v).1
    omega
  have hsplit := secProd_eq_secVal_mul s k u Za v (fun w => (Sa w).1) hZav
  have hUZa' : secProd s k u (Za - Finsupp.single v (1 : ℤ)) ≠ 0 := by
    intro h0; apply hUZa; rw [hsplit, h0, mul_zero]
  refine ⟨hFBa, hsv, ?_⟩

  have hn := congrArg (fun x => ‖σ x‖) hCR
  simp only [map_mul, map_pow, norm_mul, norm_pow, hsplit] at hn
  have p1 := norm_pos_iff.2 ((map_ne_zero σ).2 hFBa)
  have p2 := norm_pos_iff.2 ((map_ne_zero σ).2 hFZcb)
  have p3 := norm_pos_iff.2 ((map_ne_zero σ).2 hFZac)
  have p4 := norm_pos_iff.2 ((map_ne_zero σ).2 hUZb)
  have p5 := norm_pos_iff.2 ((map_ne_zero σ).2 hFBb)
  have p6 := norm_pos_iff.2 ((map_ne_zero σ).2 hFZca)
  have p7 := norm_pos_iff.2 ((map_ne_zero σ).2 hFZbc)
  have p8 := norm_pos_iff.2 ((map_ne_zero σ).2 hsv)
  have p9 := norm_pos_iff.2 ((map_ne_zero σ).2 hUZa')
  have hlog := congrArg Real.log hn
  have q2k := (pow_pos p2 k).ne'
  have q3k := (pow_pos p3 k).ne'
  have q6k := (pow_pos p6 k).ne'
  have q7k := (pow_pos p7 k).ne'
  have q12 := (mul_pos p1 (pow_pos p2 k)).ne'
  have q123 := (mul_pos (mul_pos p1 (pow_pos p2 k)) (pow_pos p3 k)).ne'
  have q56 := (mul_pos p5 (pow_pos p6 k)).ne'
  have q567 := (mul_pos (mul_pos p5 (pow_pos p6 k)) (pow_pos p7 k)).ne'
  have q89 := (mul_pos p8 p9).ne'
  rw [Real.log_mul q123 p4.ne', Real.log_mul q12 q3k, Real.log_mul p1.ne' q2k, Real.log_pow, Real.log_pow,
    Real.log_mul q567 q89, Real.log_mul q56 q7k, Real.log_mul p5.ne' q6k, Real.log_pow, Real.log_pow,
    Real.log_mul p8.ne' p9.ne'] at hlog
  simp only [I]
  linarith

theorem ciSup_chowForm_le_of_forall_admissible (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (c : Fin r → AlgebraicClosure ℚ) (Zc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hc : linSec s c ≠ 0)
    (hZc : ∀ w, Zc w = w.ord (linSec s c) + embDivisor N w) (hBZc : ∀ w, B w = 0 ∨ Zc w = 0)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hBv : B v = 0) (hZcv : Zc v = 0) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), linSec s a ≠ 0 →
      (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) → (∑ i, evalVec s v i * a i = 0) →
      (∀ w, Za w = 0 ∨ Zc w = 0) → (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) →
      ‖σ (MvPolynomial.eval a (chowForm s B))‖ / (⨆ i, ‖σ (a i)‖) ^ (B.sum fun _ n => n.toNat) ≤ R) :
    (⨆ a : {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0},
        ‖σ (MvPolynomial.eval a.1 (chowForm s B))‖ / (⨆ i, ‖σ (a.1 i)‖) ^ (B.sum fun _ n => n.toNat)) ≤ R := by
  classical
  have hr := r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N

  rcases isEmpty_or_nonempty
      {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0} with hE | hNE
  · rw [Real.iSup_of_isEmpty]; exact hR
  refine ciSup_le fun a₀ => ?_
  obtain ⟨hav₀, ha₀0⟩ := a₀.2
  by_cases hF0 : MvPolynomial.eval a₀.1 (chowForm s B) = 0
  · rw [hF0, map_zero, norm_zero, zero_div]; exact hR

  set T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := B.support ∪ Zc.support with hT
  have hTv : ∀ w ∈ T, w ≠ v := by
    intro w hw hwv
    subst hwv
    rcases Finset.mem_union.1 hw with h' | h'
    · exact (Finsupp.mem_support_iff.1 h') hBv
    · exact (Finsupp.mem_support_iff.1 h') hZcv

  obtain ⟨a', hav', haT'⟩ : ∃ a' : Fin r → AlgebraicClosure ℚ,
      L2lin.dot (evalVec s v) a' = 0 ∧ ∀ w ∈ T, L2lin.dot (evalVec s w) a' ≠ 0 := by
    obtain ⟨a', h1, h2⟩ := L2lin.exists_avoid (evalVec s v) (T.image fun w => evalVec s w) (by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      have hne := ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs v w (hTv w hw).symm
      obtain ⟨p, hp⟩ : ∃ p, chordVec s v w p ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (funext hcon)
      refine ⟨Pi.single p.2 (evalVec s v p.1) - Pi.single p.1 (evalVec s v p.2), ?_, ?_⟩
      · simp only [L2lin.dot, Pi.sub_apply, Pi.single_apply, mul_sub, mul_ite, mul_zero,
          Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
      · simp only [L2lin.dot, Pi.sub_apply, Pi.single_apply, mul_sub, mul_ite, mul_zero,
          Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        intro h0
        apply hp
        simp only [chordVec]
        linear_combination h0)
    exact ⟨a', h1, fun w hw => h2 _ (Finset.mem_image_of_mem _ hw)⟩

  set bad : Set (AlgebraicClosure ℚ) :=
    {t | ∃ x ∈ T.image (fun w => evalVec s w), L2lin.dot x (a₀.1 + t • a') = 0} ∪ {t | a₀.1 + t • a' = 0}
    with hbad_def
  have hbad : bad.Finite :=
    (L2lin.finite_bad a₀.1 a' _ (fun x hx => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      exact haT' w hw)).union (L2lin.finite_eq_zero a₀.1 a' ha₀0)

  set tseq : ℕ → AlgebraicClosure ℚ := fun n => ((n : AlgebraicClosure ℚ) + 2)⁻¹ with htseq
  have htpos : ∀ n : ℕ, ((n : AlgebraicClosure ℚ) + 2) ≠ 0 := fun n => by
    have : ((n : AlgebraicClosure ℚ) + 2) = ((n + 2 : ℕ) : AlgebraicClosure ℚ) := by push_cast; ring
    rw [this]; exact Nat.cast_ne_zero.2 (by omega)
  have tinj : Function.Injective tseq := by
    intro m n h
    simp only [htseq] at h
    have := inv_injective h
    have h' : (m : AlgebraicClosure ℚ) = n := add_right_cancel this
    exact_mod_cast h'
  have hev : ∀ᶠ n in Filter.atTop, tseq n ∉ bad := by
    have hfin : (tseq ⁻¹' bad).Finite := hbad.preimage tinj.injOn
    rcases hfin.bddAbove with ⟨N₀, hN₀⟩
    filter_upwards [Filter.eventually_gt_atTop N₀] with n hn hmem
    exact absurd (hN₀ hmem) (not_le.2 hn)

  set q : (Fin r → AlgebraicClosure ℚ) → ℝ := fun a =>
    ‖σ (MvPolynomial.eval a (chowForm s B))‖ / (⨆ i, ‖σ (a i)‖) ^ (B.sum fun _ n => n.toNat) with hq

  have hgood : ∀ᶠ n in Filter.atTop, q (a₀.1 + tseq n • a') ≤ R := by
    filter_upwards [hev] with n hn
    have ha0 : a₀.1 + tseq n • a' ≠ 0 := fun h0 => hn (Or.inr h0)
    have haT : ∀ w ∈ T, ∑ i, evalVec s w i * (a₀.1 + tseq n • a') i ≠ 0 := fun w hw h0 =>
      hn (Or.inl ⟨_, Finset.mem_image_of_mem _ hw, h0⟩)
    have hav : ∑ i, evalVec s v i * (a₀.1 + tseq n • a') i = 0 := by
      change L2lin.dot _ _ = 0
      rw [L2lin.dot_add, L2lin.dot_smul, hav', mul_zero, add_zero]
      exact hav₀
    have hla : linSec s (a₀.1 + tseq n • a') ≠ 0 := fun h0 =>
      ha0 (funext fun i => (Fintype.linearIndependent_iff.1 hs.1 _ h0) i)
    obtain ⟨D, hD, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor
      (linSec s (a₀.1 + tseq n • a')) hla
    have hZa : ∀ w, (D + embDivisor N) w = w.ord (linSec s (a₀.1 + tseq n • a')) + embDivisor N w :=
      fun w => by rw [Finsupp.add_apply, hD w]
    have haZc : ∀ w, (D + embDivisor N) w = 0 ∨ Zc w = 0 := fun w => by
      by_cases hZcw : Zc w = 0
      · exact Or.inr hZcw
      · exact Or.inl ((hypSec_eq_zero_iff N s hs _ hla _ hZa w).2
          (haT w (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 hZcw))))
    have haB : ∀ w, w ≠ v → (D + embDivisor N) w = 0 ∨ B w = 0 := fun w _ => by
      by_cases hBw : B w = 0
      · exact Or.inr hBw
      · exact Or.inl ((hypSec_eq_zero_iff N s hs _ hla _ hZa w).2
          (haT w (Finset.mem_union_left _ (Finsupp.mem_support_iff.2 hBw))))
    exact h _ _ hla hZa hav haZc haB

  have hσt : Filter.Tendsto (fun n : ℕ => σ (tseq n)) Filter.atTop (nhds 0) := by
    have e : ∀ n : ℕ, σ (tseq n) = (((n : ℝ) + 2)⁻¹ : ℝ) := by
      intro n
      simp only [htseq]
      rw [map_inv₀, map_add, map_natCast, map_ofNat]
      push_cast
      rfl
    simp_rw [e]
    rw [← Complex.ofReal_zero]
    refine (Complex.continuous_ofReal.tendsto 0).comp ?_
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hcoord : ∀ i, Filter.Tendsto (fun n => σ ((a₀.1 + tseq n • a') i)) Filter.atTop (nhds (σ (a₀.1 i))) := by
    intro i
    have : ∀ n, σ ((a₀.1 + tseq n • a') i) = σ (a₀.1 i) + σ (tseq n) * σ (a' i) := fun n => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    simp_rw [this]
    have h1 := (hσt.mul tendsto_const_nhds (b := σ (a' i))).const_add (σ (a₀.1 i))
    rw [zero_mul, add_zero] at h1
    exact h1
  have hnum : Filter.Tendsto (fun n => ‖σ (MvPolynomial.eval (a₀.1 + tseq n • a') (chowForm s B))‖)
      Filter.atTop (nhds ‖σ (MvPolynomial.eval a₀.1 (chowForm s B))‖) := by
    have e : ∀ a : Fin r → AlgebraicClosure ℚ, σ (MvPolynomial.eval a (chowForm s B))
        = MvPolynomial.eval (σ ∘ a) (MvPolynomial.map σ (chowForm s B)) := fun a => by
      rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
      rfl
    simp_rw [e]
    refine ((MvPolynomial.continuous_eval _).tendsto _ |>.comp ?_).norm
    rw [tendsto_pi_nhds]
    exact hcoord
  have hden : Filter.Tendsto (fun n => (⨆ i, ‖σ ((a₀.1 + tseq n • a') i)‖) ^ (B.sum fun _ n => n.toNat))
      Filter.atTop (nhds ((⨆ i, ‖σ (a₀.1 i)‖) ^ (B.sum fun _ n => n.toNat))) := by
    refine Filter.Tendsto.pow ?_ _
    have e1 : ∀ u : Fin r → ℝ, (⨆ i, u i) = Finset.univ.sup' Finset.univ_nonempty u := fun u =>
      (Finset.sup'_univ_eq_ciSup u).symm
    simp only [e1]
    exact Filter.Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty fun i _ => (hcoord i).norm
  have hden0 : (⨆ i, ‖σ (a₀.1 i)‖) ^ (B.sum fun _ n => n.toNat) ≠ 0 := by
    refine pow_ne_zero _ (ne_of_gt ?_)
    obtain ⟨i, hi⟩ : ∃ i, a₀.1 i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha₀0 (funext hcon)
    exact (norm_pos_iff.2 ((map_ne_zero σ).2 hi)).trans_le
      (le_ciSup (Finite.bddAbove_range fun i => ‖σ (a₀.1 i)‖) i)
  have hlim : Filter.Tendsto (fun n => q (a₀.1 + tseq n • a')) Filter.atTop (nhds (q a₀.1)) := by
    simp only [hq]
    exact hnum.div hden hden0
  exact le_of_tendsto hlim hgood

theorem exists_hypSec_off (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :
    ∃ (e : Fin r → AlgebraicClosure ℚ) (Ze : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s e ≠ 0 ∧ (∀ w, Ze w = w.ord (linSec s e) + embDivisor N w) ∧ ∀ w ∈ T, Ze w = 0 := by
  classical
  have hr := r_pos N s hs
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N

  obtain ⟨e, -, he⟩ := L2lin.exists_avoid (0 : Fin r → AlgebraicClosure ℚ) (T.image fun w => evalVec s w) (by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    refine ⟨Pi.single (pivotIndex s w hr) 1, by simp [L2lin.dot], ?_⟩
    simp only [L2lin.dot, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [evalVec_pivotIndex s w hr (s_ne_zero N s hs _)]
    exact one_ne_zero)
  have hT : T.Nonempty ∨ T = ∅ := T.eq_empty_or_nonempty.symm

  by_cases hT0 : T = ∅
  · subst hT0
    have hw := cuspInftyBar N
    refine ⟨Pi.single (pivotIndex s (cuspInftyBar N) hr) 1, ?_⟩
    have hla : linSec s (Pi.single (pivotIndex s (cuspInftyBar N) hr) 1) ≠ 0 := by
      intro h0
      have := (Fintype.linearIndependent_iff.1 hs.1 _ h0) (pivotIndex s (cuspInftyBar N) hr)
      simp at this
    obtain ⟨D, hD, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ hla
    exact ⟨D + embDivisor N, hla, fun w => by rw [Finsupp.add_apply, hD w], fun w hw => by simp at hw⟩
  · obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.2 hT0
    have he0 : e ≠ 0 := by
      intro h0
      apply he _ (Finset.mem_image_of_mem _ hw₀)
      rw [h0, L2lin.dot_zero]
    have hla : linSec s e ≠ 0 := fun h0 => he0 (funext fun i => (Fintype.linearIndependent_iff.1 hs.1 _ h0) i)
    obtain ⟨D, hD, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ hla
    refine ⟨e, D + embDivisor N, hla, fun w => by rw [Finsupp.add_apply, hD w], fun w hw => ?_⟩
    exact (hypSec_eq_zero_iff N s hs e hla _ (fun w => by rw [Finsupp.add_apply, hD w]) w).2
      (he _ (Finset.mem_image_of_mem _ hw))

theorem exists_aux (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (k : ℕ) (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    ∃ (c c' b : Fin r → AlgebraicClosure ℚ) (Zc Zc' Zb : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s c ≠ 0 ∧ (∀ w, Zc w = w.ord (linSec s c) + embDivisor N w) ∧ (∀ w, B w = 0 ∨ Zc w = 0) ∧
      linSec s c' ≠ 0 ∧ (∀ w, Zc' w = w.ord (linSec s c') + embDivisor N w) ∧ (∀ w, B w = 0 ∨ Zc' w = 0) ∧
      (∀ w, Zc w = 0 ∨ Zc' w = 0) ∧
      linSec s b ≠ 0 ∧ (∀ w, Zb w = w.ord (linSec s b) + embDivisor N w) ∧
      (∀ w, Zb w = 0 ∨ B w = 0) ∧ (∀ w, Zb w = 0 ∨ Zc w = 0) ∧ (∀ w, Zb w = 0 ∨ Zc' w = 0) := by
  classical
  have key := exists_hypSec_off N s hs

  obtain ⟨c, Zc, hc, hZc, hcT⟩ := key B.support
  obtain ⟨c', Zc', hc', hZc', hc'T⟩ := key (B.support ∪ Zc.support)
  obtain ⟨b, Zb, hb, hZb, hbT⟩ := key (B.support ∪ Zc.support ∪ Zc'.support)
  have off : ∀ (Z X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (w ∈ X.support → Z w = 0) → X w = 0 ∨ Z w = 0 := fun Z X w himp => by
    by_cases hX : X w = 0
    · exact Or.inl hX
    · exact Or.inr (himp (Finsupp.mem_support_iff.2 hX))
  refine ⟨c, c', b, Zc, Zc', Zb, hc, hZc, fun w => off Zc B w (hcT w), hc', hZc',
    fun w => off Zc' B w (fun hw => hc'T w (Finset.mem_union_left _ hw)),
    fun w => off Zc' Zc w (fun hw => hc'T w (Finset.mem_union_right _ hw)),
    hb, hZb, ?_, ?_, ?_⟩
  · intro w
    rcases off Zb B w (fun hw => hbT w (Finset.mem_union_left _ (Finset.mem_union_left _ hw))) with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · intro w
    rcases off Zb Zc w (fun hw => hbT w (Finset.mem_union_left _ (Finset.mem_union_right _ hw))) with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · intro w
    rcases off Zb Zc' w (fun hw => hbT w (Finset.mem_union_right _ hw)) with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1

theorem exists_place_off (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (B Zc Zc' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 ∧ Zc v = 0 ∧ Zc' v = 0 := by
  classical
  obtain ⟨e, Ze, he, hZe, hoff⟩ := exists_hypSec_off N s hs (B.support ∪ Zc.support ∪ Zc'.support)
  have hsum := ModularCurve.JZero.sum_toNat_hyperplaneSection_eq_embDegree N s hs e he Ze hZe
  have hpos : 0 < Ze.sum fun _ n => n.toNat := by
    rw [hsum]; unfold embDegree; omega
  obtain ⟨w, hw, hne⟩ : ∃ w ∈ Ze.support, (Ze w).toNat ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : (Ze.sum fun _ n => n.toNat) = 0 := Finset.sum_eq_zero hcon
    omega
  have hZw : Ze w ≠ 0 := Finsupp.mem_support_iff.1 hw
  have hwT : w ∉ B.support ∪ Zc.support ∪ Zc'.support := fun h => hZw (hoff w h)
  simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hwT
  exact ⟨w, hwT.1.1, hwT.1.2, hwT.2⟩

theorem core (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (hCRB : ChowReciprocity s (embDivisor N) k u B)
    (c : Fin r → AlgebraicClosure ℚ) (Zc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hc : linSec s c ≠ 0)
    (hZc : ∀ w, Zc w = w.ord (linSec s c) + embDivisor N w) (hBZc : ∀ w, B w = 0 ∨ Zc w = 0)
    (b : Fin r → AlgebraicClosure ℚ) (Zb : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hb : linSec s b ≠ 0)
    (hZb : ∀ w, Zb w = w.ord (linSec s b) + embDivisor N w)
    (hZbB : ∀ w, Zb w = 0 ∨ B w = 0) (hZbZc : ∀ w, Zb w = 0 ∨ Zc w = 0)
    (c₁ M : ℝ) (hUL : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 → Zc v = 0 →
        (∀ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
            linSec s a ≠ 0 → (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) →
            (∑ i, evalVec s v i * a i = 0) → (∀ w, Za w = 0 ∨ Zc w = 0) →
            (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) →
            Real.log ‖σ (secProd s k u (Za - Finsupp.single v (1 : ℤ)))‖
              + k * (Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
                  - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
              - k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖
            ≤ M - k * Real.log (⨆ i, ‖σ (evalVec s v i)‖) + c₁ * k) ∧
        (∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
            linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
            (∑ i, evalVec s v i * a i = 0) ∧ (∀ w, Za w = 0 ∨ Zc w = 0) ∧
            (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
            M - k * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - c₁ * k ≤
            Real.log ‖σ (secProd s k u (Za - Finsupp.single v (1 : ℤ)))‖
              + k * (Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
                  - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
              - k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hBv : B v = 0) (hZcv : Zc v = 0) :
    |chowSide (fun a => ‖σ a‖) s B v
        - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - Real.log ‖σ (secVal s v k u)‖
            - (I s σ k u B Zb Zc b c + M
                - (B.sum fun w n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s w i)‖))))| ≤ c₁ * k := by
  classical
  set ν : AlgebraicClosure ℚ → ℝ := fun a => ‖σ a‖ with hν
  set degB : ℕ := B.sum fun _ n => n.toNat with hdegB
  have hdeg : degB = k * embDegree N := ModularCurve.JZero.sum_toNat_sectionCycle_eq_mul_embDegree N k u hu huL B hB
  set Lv : ℝ := Real.log (⨆ i, ‖σ (evalVec s v i)‖) with hLv
  set Ssum : ℝ := B.sum fun w n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s w i)‖) with hSsum
  set I₀ : ℝ := I s σ k u B Zb Zc b c with hI₀

  set q : {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0} → ℝ :=
    fun a => ‖σ (MvPolynomial.eval a.1 (chowForm s B))‖ / (⨆ i, ‖σ (a.1 i)‖) ^ degB with hq
  have hbdd : BddAbove (Set.range q) := AlgebraicCurve.bddAbove_chowLogAt_range σ s B v
  have hchow : chowLogAt ν s B v = Real.log (⨆ a, q a) := rfl
  obtain ⟨hU, hL⟩ := hUL v hBv hZcv

  have hsup_pos : ∀ a : Fin r → AlgebraicClosure ℚ, a ≠ 0 → 0 < ⨆ i, ‖σ (a i)‖ := by
    intro a ha0
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha0 (funext hcon)
    have : 0 < ‖σ (a i)‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hi)
    exact this.trans_le (le_ciSup (Finite.bddAbove_range fun i => ‖σ (a i)‖) i)

  have hlogq : ∀ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s a ≠ 0 → (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) →
      (∑ i, evalVec s v i * a i = 0) → (∀ w, Za w = 0 ∨ Zc w = 0) → (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) →
      0 < ‖σ (MvPolynomial.eval a (chowForm s B))‖ / (⨆ i, ‖σ (a i)‖) ^ degB ∧
      secVal s v k u ≠ 0 ∧
      Real.log (‖σ (MvPolynomial.eval a (chowForm s B))‖ / (⨆ i, ‖σ (a i)‖) ^ degB)
        = I₀ + Real.log ‖σ (secVal s v k u)‖
          + (Real.log ‖σ (secProd s k u (Za - Finsupp.single v (1 : ℤ)))‖
              + k * (Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
                  - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
              - k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖) := by
    intro a Za ha hZa hav haZc haB
    obtain ⟨hFa, hsv, hlog⟩ := log_chowForm_eq N s hs σ k u hu huL B hB hCRB c Zc hc hZc hBZc b Zb hb hZb hZbB hZbZc
      v hBv hZcv a Za ha hZa hav haZc haB
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (linSec_zero s)
    have hnum : 0 < ‖σ (MvPolynomial.eval a (chowForm s B))‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hFa)
    have hden : 0 < (⨆ i, ‖σ (a i)‖) ^ degB := pow_pos (hsup_pos a ha0) _
    refine ⟨div_pos hnum hden, hsv, ?_⟩
    rw [Real.log_div hnum.ne' hden.ne', Real.log_pow, hlog, hdeg]
    push_cast
    ring

  obtain ⟨a, Za, ha, hZa, hav, haZc, haB, hLa⟩ := hL
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (linSec_zero s)
  obtain ⟨hqa_pos, hsv, hqa⟩ := hlogq a Za ha hZa hav haZc haB
  have hqa_le : ‖σ (MvPolynomial.eval a (chowForm s B))‖ / (⨆ i, ‖σ (a i)‖) ^ degB ≤ ⨆ a, q a :=
    le_ciSup hbdd ⟨a, hav, ha0⟩
  have hsup_q_pos : 0 < ⨆ a, q a := hqa_pos.trans_le hqa_le
  have hlow : I₀ + Real.log ‖σ (secVal s v k u)‖ + (M - k * Lv - c₁ * k) ≤ chowLogAt ν s B v := by
    rw [hchow]
    refine le_trans ?_ (Real.log_le_log hqa_pos hqa_le)
    rw [hqa]
    linarith

  set Rlog : ℝ := I₀ + Real.log ‖σ (secVal s v k u)‖ + (M - k * Lv + c₁ * k) with hRlog
  have hupper_q : (⨆ a, q a) ≤ Real.exp Rlog := by
    refine ciSup_chowForm_le_of_forall_admissible N s hs σ k u hu huL B hB c Zc hc hZc hBZc v hBv hZcv
      (Real.exp Rlog) (Real.exp_pos _).le ?_
    intro a' Za' ha' hZa' hav' haZc' haB'
    obtain ⟨hq'pos, -, hq'⟩ := hlogq a' Za' ha' hZa' hav' haZc' haB'
    rw [← hdegB]
    rw [← Real.exp_log hq'pos, Real.exp_le_exp, hq']
    have := hU a' Za' ha' hZa' hav' haZc' haB'
    linarith
  have hup : chowLogAt ν s B v ≤ Rlog := by
    rw [hchow]
    calc Real.log (⨆ a, q a) ≤ Real.log (Real.exp Rlog) := Real.log_le_log hsup_q_pos hupper_q
      _ = Rlog := Real.log_exp _

  have hcs : chowSide ν s B v = Ssum - chowLogAt ν s B v := rfl
  rw [hcs]
  rw [abs_le]
  constructor <;> linarith

end L2

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      (∀ (k' : ℕ) (u' : modularFunctionFieldBar N)
          (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          u' ≠ 0 → u' ∈ riemannRochSpace ((k' : ℤ) • embDivisor N) →
          (∀ w, B' w = w.ord u' + ((k' : ℤ) • embDivisor N) w) →
          ChowReciprocity s (embDivisor N) k' u' B') →
      ∃ m : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |chowSide (fun a => ‖σ a‖) s B v
              - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖)
                  - Real.log ‖σ (secVal s v k u)‖ - m)|
            ≤ c * k := by
  classical
  obtain ⟨c₁, hWc⟩ := ModularCurve.JZero.pencil_secProd_chowForm_two_sided N s hs
  refine ⟨3 * max c₁ 0, ?_⟩
  intro σ k u hu huL B hB hCR
  have hCRB : ChowReciprocity s (embDivisor N) k u B := hCR k u B hu huL hB
  obtain ⟨c, c', b, Zc, Zc', Zb, hc, hZc, hBZc, hc', hZc', hBZc', hZcZc', hb, hZb, hZbB, hZbZc, hZbZc'⟩ :=
    L2.exists_aux N s hs k u hu huL B hB
  obtain ⟨M, hM⟩ := hWc σ k u hu huL B hB hCR c Zc hc hZc hBZc
  obtain ⟨M', hM'⟩ := hWc σ k u hu huL B hB hCR c' Zc' hc' hZc' hBZc'
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc₁ : c₁ * k ≤ max c₁ 0 * k := mul_le_mul_of_nonneg_right (le_max_left _ _) hk
  have h0k : 0 ≤ max c₁ 0 * k := mul_nonneg (le_max_right _ _) hk
  have core1 := fun v hBv hZcv =>
    L2.core N s hs σ k u hu huL B hB hCRB c Zc hc hZc hBZc b Zb hb hZb hZbB hZbZc c₁ M hM v hBv hZcv
  have core2 := fun v hBv hZcv =>
    L2.core N s hs σ k u hu huL B hB hCRB c' Zc' hc' hZc' hBZc' b Zb hb hZb hZbB hZbZc' c₁ M' hM' v hBv hZcv

  obtain ⟨v₀, hBv₀, hZcv₀, hZc'v₀⟩ := L2.exists_place_off N s hs B Zc Zc'
  have h1 := core1 v₀ hBv₀ hZcv₀
  have h2 := core2 v₀ hBv₀ hZc'v₀
  rw [abs_le] at h1 h2
  refine ⟨L2.I s σ k u B Zb Zc b c + M
      - (B.sum fun w n => (n : ℝ) * Real.log (⨆ i, ‖σ (evalVec s w i)‖)), fun v hBv => ?_⟩
  rcases eq_or_ne (Zc v) 0 with hZcv | hZcv
  · have h := core1 v hBv hZcv
    rw [abs_le] at h ⊢
    constructor <;> linarith
  · have hZc'v : Zc' v = 0 := (hZcZc' v).resolve_left hZcv
    have h := core2 v hBv hZc'v
    rw [abs_le] at h ⊢
    constructor <;> linarith

end S_ModularCurve_JZero_chowSide_arch_embedding_off_support
end P2MW
export P2MW.S_ModularCurve_JZero_chowSide_arch_embedding_off_support (solution)
