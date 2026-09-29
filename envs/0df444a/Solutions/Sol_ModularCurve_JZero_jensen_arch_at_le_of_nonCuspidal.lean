-- Prove2me | solution 1 for ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/272c88ad-7bea-5866-b6a1-159c7a5b8762

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_constantsAreBase_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_JZero_exists_seq_tendsto_place
import Theorems.Thm_ModularCurve_JZero_prox_sum_le_of_forall_log_secVal_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero ModularCurve.qExpandAlgHomC_apply ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

noncomputable section

namespace P2MW

section Eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero (Q : Place K F) : Q.evalAt (0 : F) = 0 := by
  have h := Q.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

theorem ord_nonneg_of_mem (Q : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ Q.toValuationSubring) :
    0 ≤ Q.ord f := by
  have h1 : Q.adicValuation f ≤ 1 := by
    have := Q.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : Q.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := Q.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (Q.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (Q.adicValuation f))
  omega

theorem mem_of_eq_zero_or_ord_nonneg (Q : Place K F) {f : F} (h : f = 0 ∨ 0 ≤ Q.ord f) :
    f ∈ Q.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 (h.resolve_left hf0)

theorem ord_eq_zero_of_evalAt_ne_zero (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f ≠ 0) : Q.ord f = 0 := by
  have hres : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply Q.algebraMap_residueField_injective
    rw [Q.algebraMap_evalAt hQ hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := Q.ord_coe_unit u
  rwa [hu] at this

theorem ne_zero_of_evalAt_ne_zero (Q : Place K F) {f : F} (h : Q.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact h (evalAt_zero Q)

theorem evalAt_eq_zero_of_ord_pos (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) : Q.evalAt f = 0 := by
  by_contra hne
  have := ord_eq_zero_of_evalAt_ne_zero Q hQ hf hne
  omega

theorem ord_pos_of_evalAt_eq_zero (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f = 0) : 0 < Q.ord f := by
  rcases (ord_nonneg_of_mem Q hf0 hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (Q.evalAt_ne_zero_of_ord_eq_zero hQ hf0 heq.symm)

theorem evalAt_add_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f + g) = Q.evalAt f + Q.evalAt g := by
  apply Q.algebraMap_residueField_injective
  rw [map_add, Q.algebraMap_evalAt hQ (add_mem hf hg), Q.algebraMap_evalAt hQ hf, Q.algebraMap_evalAt hQ hg,
    ← map_add]
  rfl

theorem evalAt_neg_of_mem (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf : f ∈ Q.toValuationSubring) :
    Q.evalAt (-f) = -Q.evalAt f := by
  apply Q.algebraMap_residueField_injective
  rw [map_neg, Q.algebraMap_evalAt hQ (neg_mem hf), Q.algebraMap_evalAt hQ hf, ← map_neg]
  rfl

theorem evalAt_sub_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f - g) = Q.evalAt f - Q.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem Q hQ hf (neg_mem hg), evalAt_neg_of_mem Q hQ hg, ← sub_eq_add_neg]

theorem smul_mem_of_mem (Q : Place K F) (a : K) {f : F} (hf : f ∈ Q.toValuationSubring) :
    a • f ∈ Q.toValuationSubring := by
  rw [Algebra.smul_def]; exact mul_mem (Q.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (Q : Place K F) (hQ : Q.IsRational) (a : K) {f : F}
    (hf : f ∈ Q.toValuationSubring) : Q.evalAt (a • f) = a * Q.evalAt f := by
  rw [Algebra.smul_def, Q.evalAt_mul_of_mem hQ (Q.algebraMap_mem' a) hf, Q.evalAt_algebraMap_eq]

theorem evalAt_sum_smul_of_mem {ι : Type*} (S : Finset ι) (Q : Place K F) (hQ : Q.IsRational)
    (c : ι → K) {f : ι → F} (hf : ∀ i, f i ∈ Q.toValuationSubring) :
    Q.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * Q.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact evalAt_zero Q
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem Q hQ (smul_mem_of_mem Q _ (hf a)) (sum_mem fun i _ => smul_mem_of_mem Q _ (hf i)),
      evalAt_smul_of_mem Q hQ _ (hf a), ih]

theorem inv_mem_of_ord_eq_zero (Q : Place K F) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    f⁻¹ ∈ Q.toValuationSubring :=
  Q.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf0) (by rw [Q.ord_inv, h, neg_zero])

theorem evalAt_mul_evalAt_inv (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    Q.evalAt f * Q.evalAt f⁻¹ = 1 := by
  rw [← Q.evalAt_mul_of_mem hQ (Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.ge) (inv_mem_of_ord_eq_zero Q hf0 h),
    mul_inv_cancel₀ hf0, Q.evalAt_one]

theorem exists_ord_eq_one (Q : Place K F) : ∃ t : F, Q.ord t = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  exact ⟨(π : F), Q.ord_coe_irreducible hπ⟩

end Eval

end P2MW

end

namespace P2MW

open AlgebraicCurve ModularCurve KaehlerDifferential

section Generic2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_notMem {D : Divisor K F} {f : F} (hf : f ∉ riemannRochSpace D) : f ≠ 0 := by
  rintro rfl; exact hf (zero_mem _)

theorem ord_eq_of_mem_notMem {D : Divisor K F} {f : F} (w : Place K F)
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    w.ord f + D w = 0 := by
  classical
  have hf0 := ne_zero_of_notMem hf'
  have hge : -D w ≤ w.ord f := ((mem_riemannRochSpace_iff.mp hf) w).resolve_left hf0
  have hlt : w.ord f < -D w + 1 := by
    by_contra hge'
    push Not at hge'
    apply hf'
    rw [mem_riemannRochSpace_iff]
    intro v
    by_cases hv : v = w
    · subst hv; right
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]; linarith
    · rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
      · exact Or.inl h
      · right
        rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]; exact h
  omega

theorem mem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (i : ι) : x i ∈ riemannRochSpace D :=
  hspan ▸ Submodule.subset_span ⟨i, rfl⟩

theorem exists_mem_notMem_of_finrank_ne (D : Divisor K F) (w : Place K F)
    (h : Module.finrank K (riemannRochSpace D) ≠
      Module.finrank K (riemannRochSpace (D - Finsupp.single w 1))) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  classical
  have hle : riemannRochSpace (D - Finsupp.single w 1) ≤ riemannRochSpace D := by
    refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_)
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hne : riemannRochSpace (D - Finsupp.single w 1) ≠ riemannRochSpace D := by
    intro heq; exact h (by rw [heq])
  obtain ⟨f, hf, hnf⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨f, hf, hnf⟩

theorem exists_forall_ord_le {r : ℕ} (hr : 0 < r) (s : Fin r → F) (v : Place K F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_eq_neg_of_forall_le {r : ℕ} (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0) {D : Divisor K F}
    (hsD : ∀ i, s i ∈ riemannRochSpace D) (w : Place K F) (hbpf : ∃ i, w.ord (s i) + D w = 0)
    (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j)) : w.ord (s p) = -D w := by
  obtain ⟨i, hi⟩ := hbpf
  have h1 := hp i
  have h2 : -D w ≤ w.ord (s p) := ((mem_riemannRochSpace_iff.mp (hsD p)) w).resolve_left (hs0 p)
  omega

end Generic2

section Bar

variable (N : ℕ) [NeZero N]

theorem ell_eq_bar [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    functionFieldRiemannRoch_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  have hdegK := degree_canonicalDivisorOf_modularFunctionFieldBar N hω
  have hgen := genus_eq_genusFF_modularFunctionFieldBar N
  have h1 := hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hgen]; linarith
  have hell : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell, hgen] at h1
  push_cast at h1
  linarith

scoped instance finiteDimensional_lSpace_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : FiniteDimensional (AlgebraicClosure ℚ) (LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase _ _
      (constantsAreBase_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N)
  exact finiteDimensional_lSpace D

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

theorem exists_mem_notMem_bar [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  apply exists_mem_notMem_of_finrank_ne
  have e1 := ell_eq_bar N D (by omega)
  have hdeg' : Divisor.degree (D - Finsupp.single w 1) = Divisor.degree D - 1 := by
    rw [map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N w]; push_cast; ring
  have e2 := ell_eq_bar N (D - Finsupp.single w 1) (by rw [hdeg']; omega)
  rw [hdeg'] at e2
  intro heq
  have : (ell D : ℤ) = (ell (D - Finsupp.single w 1) : ℤ) := by
    unfold ell LSpace; exact_mod_cast heq
  omega

theorem bpf_of_span_eq [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    {ι : Type*} (x : ι → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (x i) + D w = 0 := by
  intro w
  obtain ⟨f, hf, hf'⟩ := exists_mem_notMem_bar N D hD w
  have : ∃ i, x i ∉ riemannRochSpace (D - Finsupp.single w 1) := by
    by_contra hall
    push Not at hall
    apply hf'
    have hle : Submodule.span (AlgebraicClosure ℚ) (Set.range x) ≤ riemannRochSpace (D - Finsupp.single w 1) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    exact hle (hspan ▸ hf)
  obtain ⟨i, hi⟩ := this
  exact ⟨i, ord_eq_of_mem_notMem w (mem_of_span_eq x hspan i) hi⟩

theorem pos_of_span_eq [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    {a : ℕ} (x : Fin a → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) : 0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  subst ha0
  obtain ⟨f, hf, hf'⟩ := exists_mem_notMem_bar N D hD (cuspInftyBar N)
  have : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range x) := hspan ▸ hf
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
  exact ne_zero_of_notMem hf' this

end Bar

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

namespace P2MW

open AlgebraicCurve ModularCurve

section BarPiv

variable (N : ℕ) [NeZero N]

theorem regVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (k e : ℕ)
    (u : modularFunctionFieldBar N) :
    regVal s o t k e u = o.evalAt (u * ((s (pivotIndex s o hr))⁻¹) ^ k * (t⁻¹) ^ e) := by
  rw [regVal]; simp only [dif_pos hr]

theorem evalVec_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]; simp only [dif_pos hr]

theorem ord_pivot_le {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem exists_family_span_eq (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    [FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D)] :
    ∃ (c : ℕ) (t : Fin c → modularFunctionFieldBar N), (∀ i, t i ≠ 0) ∧
      Submodule.span (AlgebraicClosure ℚ) (Set.range t) = riemannRochSpace D := by
  let bs := Module.finBasis (AlgebraicClosure ℚ) (riemannRochSpace D)
  refine ⟨_, fun i => (bs i : modularFunctionFieldBar N), fun i => ?_, ?_⟩
  · intro h0
    apply bs.ne_zero i
    exact Subtype.ext h0
  · have hr : Set.range (fun i => (bs i : modularFunctionFieldBar N)) = (riemannRochSpace D).subtype '' Set.range bs := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, bs.span_eq, Submodule.map_top, Submodule.range_subtype]

end BarPiv
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

set_option autoImplicit false

open AlgebraicCurve ModularCurve Filter Topology

noncomputable section

namespace P2MJAU

theorem exists_embedding_of_infinitePlace (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (ν : NumberField.InfinitePlace ↥L) :
    ∃ σ : (AlgebraicClosure ℚ) →+* ℂ, ∀ a : ↥L, ν a = ‖σ (a : AlgebraicClosure ℚ)‖ := by
  letI algLC : Algebra ↥L ℂ := RingHom.toAlgebra ν.embedding
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ↥L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥L
  let σ₀ : (AlgebraicClosure ℚ) →ₐ[↥L] ℂ := IsAlgClosed.lift
  refine ⟨σ₀.toRingHom, fun a => ?_⟩
  have hcomm : σ₀.toRingHom ((a : ↥L) : AlgebraicClosure ℚ) = ν.embedding a := by
    have h1 := σ₀.commutes a
    have h3 : (algebraMap ↥L ℂ) a = ν.embedding a := by rw [RingHom.algebraMap_toAlgebra]
    rw [h3] at h1
    exact h1
  rw [hcomm]
  exact (NumberField.InfinitePlace.norm_embedding_eq ν a).symm

theorem prox_transport {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (σ : (AlgebraicClosure ℚ) →+* ℂ)
    {r : ℕ} (x y : Fin r → ↥L) (ex ey : Fin r → AlgebraicClosure ℚ)
    (hx : ∀ i, ((x i : ↥L) : AlgebraicClosure ℚ) = ex i) (hy : ∀ i, ((y i : ↥L) : AlgebraicClosure ℚ) = ey i)
    (ν : ↥L → ℝ) (hν : ∀ a : ↥L, ν a = ‖σ (a : AlgebraicClosure ℚ)‖) :
    prox ν x y = prox (fun a => ‖σ a‖) ex ey := by
  unfold prox
  have hA : (⨆ i, ν (x i)) = ⨆ i, ‖σ (ex i)‖ := iSup_congr fun i => by rw [hν, hx]
  have hB : (⨆ i, ν (y i)) = ⨆ i, ‖σ (ey i)‖ := iSup_congr fun i => by rw [hν, hy]
  have hC : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1))
      = ⨆ p : Fin r × Fin r, ‖σ (ex p.1 * ey p.2 - ex p.2 * ey p.1)‖ := by
    refine iSup_congr fun p => ?_
    rw [hν]
    congr 1
    have : ((x p.1 * y p.2 - x p.2 * y p.1 : ↥L) : AlgebraicClosure ℚ) = ex p.1 * ey p.2 - ex p.2 * ey p.1 := by
      push_cast; rw [hx, hx, hy, hy]
    rw [this]
  rw [hA, hB, hC]

variable (N : ℕ) [NeZero N]

def pointFun {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (k : ℕ) (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  (B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
    - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - Real.log ‖σ (secVal s v k u)‖)

def genFun {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (k : ℕ) (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) : ℝ :=
  ((B.erase v₀).sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w))
    - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
        + (B v₀ : ℝ) * Real.log (⨆ q : Fin r × Fin r,
            ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖)
        - Real.log ‖σ (regVal s v₀ t k (B v₀).toNat u)‖)

theorem genFun_of_apply_eq_zero {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (k : ℕ) (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (h0 : B v₀ = 0) :
    genFun N s σ k u B v₀ t = pointFun N s σ k u B v₀ := by
  classical
  unfold genFun pointFun
  have herase : B.erase v₀ = B := by
    rw [Finsupp.erase_of_notMem_support]; rwa [Finsupp.notMem_support_iff]
  have hreg : regVal s v₀ t k (B v₀).toNat u = secVal s v₀ k u := by
    rw [h0, Int.toNat_zero, regVal, secVal]
    simp only [dif_pos hr, pow_zero, mul_one]
  rw [herase, hreg, h0]
  push_cast
  ring

section Coeff

variable {N}

theorem secVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (k : ℕ) (u : modularFunctionFieldBar N) :
    secVal s v k u = v.evalAt (u * ((s (pivotIndex s v hr))⁻¹) ^ k) := by
  rw [secVal]; simp only [dif_pos hr]

theorem evalAt_prod_of_mem {ι : Type*} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : v.IsRational) (f : ι → modularFunctionFieldBar N) (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    v.evalAt (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Place.evalAt_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : f a ∈ v.toValuationSubring := hf a (Finset.mem_insert_self a S)
    have hS : ∀ i ∈ S, f i ∈ v.toValuationSubring := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ S, f i) ∈ v.toValuationSubring := Subring.prod_mem _ hS
    rw [v.evalAt_mul_of_mem hv hfa hprod, ih hS]

theorem log_secVal_le {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (σ : (AlgebraicClosure ℚ) →+* ℂ) {k : ℕ} (cf : (Fin k → Fin r) → AlgebraicClosure ℚ)
    (u : modularFunctionFieldBar N) (hu0 : u ≠ 0) (hu : u = ∑ φ : Fin k → Fin r, cf φ • ∏ l, s (φ l))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hy : B y = 0) :
    Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖)
      ≤ Real.log (⨆ φ, ‖σ (cf φ)‖) + (k : ℝ) * Real.log r := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsE : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨i₀, hi₀⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs y
  have hr : 0 < r := i₀.pos
  haveI : Nonempty (Fin r) := ⟨i₀⟩
  haveI : Nonempty (Fin k → Fin r) := ⟨fun _ => i₀⟩
  have hyr := P2MW.isRational_bar N y
  set piv := pivotIndex s y hr with hpiv
  have hp : ∀ j, y.ord (s piv) ≤ y.ord (s j) := P2MW.ord_pivot_le N hr s y
  have hordpiv : y.ord (s piv) = -(embDivisor N y) := by
    have h1 := hp i₀
    have h2 := ((mem_riemannRochSpace_iff.mp (hsE piv)) y).resolve_left (hs0 piv)
    omega
  have hratmem : ∀ i, s i * (s piv)⁻¹ ∈ y.toValuationSubring := fun i =>
    y.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 piv)))
      (by rw [Place.ord_mul _ (hs0 i) (inv_ne_zero (hs0 piv)), Place.ord_inv]; linarith [hp i])
  have hX : ∀ i, evalVec s y i = y.evalAt (s i * (s piv)⁻¹) := fun i => P2MW.evalVec_apply N hr s y i

  have hrew : u * ((s piv)⁻¹) ^ k = ∑ φ : Fin k → Fin r, cf φ • ∏ l, (s (φ l) * (s piv)⁻¹) := by
    rw [hu, Finset.sum_mul]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [smul_mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hval : secVal s y k u = ∑ φ : Fin k → Fin r, cf φ * ∏ l, evalVec s y (φ l) := by
    rw [secVal_apply hr s y k u, ← hpiv, hrew,
      P2MW.evalAt_sum_smul_of_mem Finset.univ y hyr cf (f := fun φ => ∏ l, (s (φ l) * (s piv)⁻¹)) (fun φ => Subring.prod_mem _ fun l _ => hratmem (φ l))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [evalAt_prod_of_mem Finset.univ y hyr _ (fun l _ => hratmem (φ l))]
    simp only [hX]

  have hne : secVal s y k u ≠ 0 := by
    rw [secVal_apply hr s y k u, ← hpiv]
    have hf0 : u * ((s piv)⁻¹) ^ k ≠ 0 := mul_ne_zero hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv)))
    have hord : y.ord (u * ((s piv)⁻¹) ^ k) = 0 := by
      rw [Place.ord_mul _ hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv))), ← zpow_natCast, Place.ord_zpow, Place.ord_inv,
        hordpiv]
      have := hB y
      rw [hy, Finsupp.smul_apply, smul_eq_mul] at this
      linarith
    exact y.evalAt_ne_zero_of_ord_eq_zero hyr hf0 hord

  set X : ℝ := ⨆ i, ‖σ (evalVec s y i)‖ with hXdef
  set C : ℝ := ⨆ φ, ‖σ (cf φ)‖ with hCdef
  have hXge : ∀ i, ‖σ (evalVec s y i)‖ ≤ X := fun i =>
    le_ciSup (f := fun i => ‖σ (evalVec s y i)‖) (Set.finite_range _).bddAbove i
  have hX1 : 1 ≤ X := by
    have h := hXge piv
    rwa [hX piv, mul_inv_cancel₀ (hs0 piv), Place.evalAt_one, map_one, norm_one] at h
  have hCge : ∀ φ, ‖σ (cf φ)‖ ≤ C := fun φ =>
    le_ciSup (f := fun φ => ‖σ (cf φ)‖) (Set.finite_range _).bddAbove φ
  have hC0 : 0 < C := by

    by_contra hle
    rw [not_lt] at hle
    apply hu0
    rw [hu]
    refine Finset.sum_eq_zero fun φ _ => ?_
    have : cf φ = 0 := by
      have h := (hCge φ).trans hle
      have h' : ‖σ (cf φ)‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [norm_eq_zero] at h'
      exact σ.injective (by rw [h', map_zero])
    rw [this]; simp
  have hbound : ‖σ (secVal s y k u)‖ ≤ (r : ℝ) ^ k * C * X ^ k := by
    rw [hval, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ φ : Fin k → Fin r, ‖σ (cf φ * ∏ l, evalVec s y (φ l))‖ ≤ C * X ^ k := by
      intro φ
      rw [map_mul, map_prod, norm_mul, norm_prod]
      refine mul_le_mul (hCge φ) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (le_trans (norm_nonneg _) (hCge φ))
      calc ∏ l, ‖σ (evalVec s y (φ l))‖ ≤ ∏ _l : Fin k, X :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => hXge (φ l)
        _ = X ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ∑ φ, ‖σ (cf φ * ∏ l, evalVec s y (φ l))‖ ≤ ∑ _φ : Fin k → Fin r, C * X ^ k := Finset.sum_le_sum fun φ _ => hterm φ
      _ = (r : ℝ) ^ k * C * X ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
  have hpos : 0 < ‖σ (secVal s y k u)‖ := norm_pos_iff.mpr (by rwa [map_ne_zero])
  have hlog := Real.log_le_log hpos hbound
  have hX0 : 0 < X := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hC0.ne', Real.log_pow, Real.log_pow] at hlog
  linarith

end Coeff
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

section Drop

variable {N}

theorem prox_ge_neg_log_two {r : ℕ} (σ : (AlgebraicClosure ℚ) →+* ℂ) (x y : Fin r → AlgebraicClosure ℚ)
    (hx1 : 1 ≤ ⨆ i, ‖σ (x i)‖) (hy1 : 1 ≤ ⨆ j, ‖σ (y j)‖) :
    -Real.log 2 ≤ prox (fun a => ‖σ a‖) x y := by
  haveI : Nonempty (Fin r) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [iSup_of_empty', Real.sSup_empty] at hx1
    linarith
  set Sx := ⨆ i, ‖σ (x i)‖ with hSx
  set Sy := ⨆ j, ‖σ (y j)‖ with hSy
  have hxle : ∀ i, ‖σ (x i)‖ ≤ Sx := fun i => le_ciSup (f := fun i => ‖σ (x i)‖) (Set.finite_range _).bddAbove i
  have hyle : ∀ j, ‖σ (y j)‖ ≤ Sy := fun j => le_ciSup (f := fun j => ‖σ (y j)‖) (Set.finite_range _).bddAbove j
  have hW : (⨆ q : Fin r × Fin r, ‖σ (x q.1 * y q.2 - x q.2 * y q.1)‖) ≤ 2 * Sx * Sy := by
    refine ciSup_le fun q => ?_
    rw [map_sub, map_mul, map_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖σ (x q.1)‖ * ‖σ (y q.2)‖ ≤ Sx * Sy := mul_le_mul (hxle _) (hyle _) (norm_nonneg _) (by linarith)
    have h2 : ‖σ (x q.2)‖ * ‖σ (y q.1)‖ ≤ Sx * Sy := mul_le_mul (hxle _) (hyle _) (norm_nonneg _) (by linarith)
    linarith
  have hlx : 0 ≤ Real.log Sx := Real.log_nonneg hx1
  have hly : 0 ≤ Real.log Sy := Real.log_nonneg hy1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold prox
  by_cases hW0 : (⨆ q : Fin r × Fin r, ‖σ (x q.1 * y q.2 - x q.2 * y q.1)‖) = 0
  · rw [hW0, Real.log_zero, sub_zero]; linarith
  · have hWpos : 0 < ⨆ q : Fin r × Fin r, ‖σ (x q.1 * y q.2 - x q.2 * y q.1)‖ := by
      obtain ⟨q₀⟩ : Nonempty (Fin r × Fin r) := inferInstance
      exact lt_of_le_of_ne ((norm_nonneg _).trans
        (le_ciSup (f := fun q : Fin r × Fin r => ‖σ (x q.1 * y q.2 - x q.2 * y q.1)‖) (Set.finite_range _).bddAbove q₀)) (Ne.symm hW0)
    have := Real.log_le_log hWpos hW
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)] at this
    linarith

theorem one_le_iSup_evalVec {r : ℕ} (σ : (AlgebraicClosure ℚ) →+* ℂ) (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (hs0 : ∀ i, s i ≠ 0) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : 1 ≤ ⨆ i, ‖σ (evalVec s v i)‖ := by
  have h1 : evalVec s v (pivotIndex s v hr) = 1 := by
    rw [P2MW.evalVec_apply N hr s v, mul_inv_cancel₀ (hs0 _), Place.evalAt_one]
  calc (1 : ℝ) = ‖σ (evalVec s v (pivotIndex s v hr))‖ := by rw [h1, map_one, norm_one]
    _ ≤ ⨆ i, ‖σ (evalVec s v i)‖ := le_ciSup (f := fun i => ‖σ (evalVec s v i)‖) (Set.finite_range _).bddAbove _

theorem sum_ge_sum_sub {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (D D' : Divisor (AlgebraicClosure ℚ) F) (hD'0 : ∀ w, 0 ≤ D' w) (hle : ∀ w, D' w ≤ D w)
    (P : Place (AlgebraicClosure ℚ) F → ℝ) (M : ℝ) (hM : 0 ≤ M) (hP : ∀ w, -M ≤ P w) :
    (D'.sum fun w n => (n : ℝ) * P w) - M * (D.sum fun _ n => (n : ℝ)) ≤ D.sum fun w n => (n : ℝ) * P w := by
  classical
  have hsplit : ∀ Q : Place (AlgebraicClosure ℚ) F → ℝ,
      (D.sum fun w n => (n : ℝ) * Q w) = (D'.sum fun w n => (n : ℝ) * Q w) + ((D - D').sum fun w n => (n : ℝ) * Q w) := by
    intro Q
    have : D = D' + (D - D') := by abel
    conv_lhs => rw [this]
    rw [Finsupp.sum_add_index' (fun w => by simp) (fun w a b => by push_cast; ring)]
  have hnnD : ∀ w, 0 ≤ (D - D') w := fun w => by rw [Finsupp.sub_apply]; linarith [hle w]
  have h1 : -M * ((D - D').sum fun _ n => (n : ℝ)) ≤ (D - D').sum fun w n => (n : ℝ) * P w := by
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have h0 : (0 : ℝ) ≤ ((D - D') w : ℝ) := by exact_mod_cast hnnD w
    nlinarith [hP w]
  have h2 : ((D - D').sum fun _ n => (n : ℝ)) ≤ D.sum fun _ n => (n : ℝ) := by
    have := hsplit (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    have : 0 ≤ D'.sum fun _ n => (n : ℝ) := by
      rw [Finsupp.sum]; exact Finset.sum_nonneg fun w _ => by exact_mod_cast hD'0 w
    linarith
  rw [hsplit P]
  nlinarith

end Drop
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

section Limit

theorem le_of_tendsto_of_le {f : ℕ → ℝ} {G M : ℝ} (hf : Tendsto f atTop (𝓝 G)) (h : ∀ n, f n ≤ M) : G ≤ M :=
  le_of_tendsto' hf h

theorem approach {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (jhat : modularFunctionFieldBar N)
    (hAT : ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
      v₀.ord t = 1 → (v₀ = cuspInftyBar N ∨ jhat ∈ v₀.toValuationSubring) →
      ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
        (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ e : ℕ, (e : ℤ) = v₀.ord u + k * embDivisor N v₀ →
      ∃ v : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ v₀) ∧
        (∀ w ∈ S, w ≠ v₀ → Tendsto (fun n => prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s w)) atTop
            (𝓝 (prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w)))) ∧
        Tendsto (fun n => (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖
            - (e : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s v₀)) atTop
          (𝓝 (((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
              + (e : ℝ) * Real.log (⨆ q : Fin r × Fin r,
                  ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖)
              - Real.log ‖σ (regVal s v₀ t k e u)‖)))
    (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0)
    (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N)
    (hadm : v₀ = cuspInftyBar N ∨ jhat ∈ v₀.toValuationSubring) (hpos : 0 < B v₀) (ht : v₀.ord t = 1) :
    ∃ vseq : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ n, B (vseq n) = 0) ∧ Tendsto (fun n => pointFun N s σ k u B (vseq n)) atTop (𝓝 (genFun N s σ k u B v₀ t)) := by
  classical
  set e : ℕ := (B v₀).toNat with he_def
  have heZ : (e : ℤ) = B v₀ := Int.toNat_of_nonneg hpos.le
  have heR : (e : ℝ) = (B v₀ : ℝ) := by exact_mod_cast heZ
  have he : (e : ℤ) = v₀.ord u + k * embDivisor N v₀ := by rw [heZ, hB v₀, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨v, hvS, -, hprox, hcore⟩ := hAT v₀ t ht hadm σ B.support k u hu0 hu e he
  refine ⟨v, fun n => Finsupp.notMem_support_iff.mp (hvS n), ?_⟩
  have hv₀mem : v₀ ∈ B.support := Finsupp.mem_support_iff.mpr (ne_of_gt hpos)
  set Pr : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ :=
    fun a b => prox (fun z => ‖σ z‖) (evalVec s a) (evalVec s b) with hPr
  have hsplit : ∀ n, pointFun N s σ k u B (v n)
      = (∑ w ∈ B.support.erase v₀, (B w : ℝ) * Pr (v n) w)
        - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖ - (e : ℝ) * Pr (v n) v₀) := by
    intro n
    unfold pointFun
    rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hv₀mem, heR]
    simp only [hPr]
    ring
  have hlimit : genFun N s σ k u B v₀ t
      = (∑ w ∈ B.support.erase v₀, (B w : ℝ) * Pr v₀ w)
        - (((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
            + (e : ℝ) * Real.log (⨆ q : Fin r × Fin r,
                ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖)
            - Real.log ‖σ (regVal s v₀ t k e u)‖) := by
    unfold genFun
    rw [Finsupp.sum, Finsupp.support_erase, heR]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]
  rw [show (fun n => pointFun N s σ k u B (v n)) = fun n => (∑ w ∈ B.support.erase v₀, (B w : ℝ) * Pr (v n) w)
        - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖ - (e : ℝ) * Pr (v n) v₀) from funext hsplit, hlimit]
  refine Tendsto.sub ?_ hcore
  refine tendsto_finsetSum _ fun w hw => ?_
  exact (hprox w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)).const_mul _

end Limit
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

end P2MJAU
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

namespace P2MJAU

open AlgebraicCurve ModularCurve Filter Topology

theorem mul_mem_rr_add {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {D₁ D₂ : Divisor (AlgebraicClosure ℚ) F}
    {f g : F} (hf : f ∈ riemannRochSpace D₁) (hg : g ∈ riemannRochSpace D₂) : f * g ∈ riemannRochSpace (D₁ + D₂) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

theorem prod_mem_rr {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] (E : Divisor (AlgebraicClosure ℚ) F) {r : ℕ}
    (s : Fin r → F) (hsE : ∀ i, s i ∈ riemannRochSpace E) :
    ∀ (k : ℕ) (φ : Fin k → Fin r), (∏ l, s (φ l)) ∈ riemannRochSpace ((k : ℤ) • E) := by
  intro k
  induction k with
  | zero =>
    intro φ
    rw [Finset.univ_eq_empty, Finset.prod_empty, Nat.cast_zero, zero_smul, mem_riemannRochSpace_iff]
    intro w; right; rw [Place.ord_one, Finsupp.zero_apply, neg_zero]
  | succ k ih =>
    intro φ
    rw [Fin.prod_univ_succ]
    have h : ((k + 1 : ℕ) : ℤ) • E = E + (k : ℤ) • E := by push_cast; rw [add_smul, one_smul, add_comm]
    rw [h]
    exact mul_mem_rr_add (hsE _) (ih fun l => φ l.succ)

set_option maxHeartbeats 6400000 in
theorem main (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
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
            + c₀ * k := by
  classical

  obtain ⟨i₀, -⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs (cuspInftyBar N)
  have hr : 0 < r := i₀.pos
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsE : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (cuspInftyBar N).toValuationSubring
  have hπ1 : (cuspInftyBar N).ord (π : modularFunctionFieldBar N) = 1 := (cuspInftyBar N).ord_coe_irreducible hπ
  obtain ⟨c, hc⟩ := ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le N s hs (π : modularFunctionFieldBar N) hπ1
  set d : ℝ := (embDegree N : ℝ) with hd
  refine ⟨c + Real.log r + d * Real.log 2, ?_⟩
  intro k L _ cL u hu0 hu_eq B hB ν v₀ hadm B' hB'0 hB'le x hxB' hx₀ t ht a ha y hy hy0

  have huE : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) := by
    rw [hu_eq]
    exact Submodule.sum_mem _ fun φ _ => Submodule.smul_mem _ _ (prod_mem_rr (embDivisor N) s hsE k φ)
  have hBnn : ∀ w, 0 ≤ B w := fun w => by
    rw [hB w]
    have := ((mem_riemannRochSpace_iff.mp huE) w).resolve_left hu0
    linarith

  obtain ⟨σ, hσ⟩ := exists_embedding_of_infinitePlace L ν

  set S : ℝ := Real.log (⨆ φ, ‖σ ((cL φ : ↥L) : AlgebraicClosure ℚ)‖) + (k : ℝ) * Real.log r with hSdef
  have hS : ∀ yy : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B yy = 0 →
      Real.log ‖σ (secVal s yy k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s yy i)‖) ≤ S :=
    fun yy hyy => log_secVal_le s hs σ (fun φ => ((cL φ : ↥L) : AlgebraicClosure ℚ)) u hu0 hu_eq B hB yy hyy
  obtain ⟨-, hpt⟩ := hc σ k u hu0 huE B hB S hS

  have hpoint : ∀ v, B v = 0 → pointFun N s σ k u B v ≤ S + c * k := by
    intro v hv
    have := hpt v hv
    unfold pointFun
    linarith

  have hgen : genFun N s σ k u B v₀ t ≤ S + c * k := by
    by_cases h0 : B v₀ = 0
    · rw [genFun_of_apply_eq_zero N hr s σ k u B v₀ t h0]; exact hpoint v₀ h0
    · have hpos : 0 < B v₀ := lt_of_le_of_ne (hBnn v₀) (Ne.symm h0)
      obtain ⟨vseq, hvseq0, hlim⟩ := approach N s (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
        (fun v₀ t ht hv₀ => ModularCurve.JZero.exists_seq_tendsto_place N s hs v₀ t ht hv₀)
        σ k u hu0 huE B hB v₀ t hadm hpos (ht hpos)
      exact le_of_tendsto_of_le hlim fun n => hpoint _ (hvseq0 n)

  have hmassB : (B.sum fun _ n => (n : ℝ)) = (k : ℝ) * d := by
    obtain ⟨Du, hDu, hDudeg⟩ := (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor u hu0
    have hBeq : B = Du + (k : ℤ) • embDivisor N := by
      ext w; rw [hB w, Finsupp.add_apply, hDu w]
    have hdeg : (B.degree : ℝ) = B.sum (fun _ n => (n : ℝ)) := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.sum]
      push_cast
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [ModularCurve.deg_eq_one_modularFunctionFieldBar N w]
    rw [← hdeg, hBeq, map_add, map_zsmul, hDudeg, zero_add, embDivisor, map_zsmul, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N, hd]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  have hmassE : ((B.erase v₀).sum fun _ n => (n : ℝ)) ≤ (k : ℝ) * d := by
    have h := Finsupp.add_sum_erase' B v₀ (fun _ n => (n : ℝ)) (fun w => by simp)
    rw [hmassB] at h
    have : (0 : ℝ) ≤ (B v₀ : ℝ) := by exact_mod_cast hBnn v₀
    linarith
  have hdrop := sum_ge_sum_sub (B.erase v₀) B' hB'0 hB'le (fun w => prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w))
    (Real.log 2) (Real.log_nonneg (by norm_num))
    (fun w => prox_ge_neg_log_two σ _ _ (one_le_iSup_evalVec σ hr s hs0 v₀) (one_le_iSup_evalVec σ hr s hs0 w))
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hdrop' : (B'.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w)) - Real.log 2 * ((k : ℝ) * d)
      ≤ (B.erase v₀).sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w) := by
    have := mul_le_mul_of_nonneg_left hmassE hl2
    linarith

  have hsum : (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
      = B'.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w) := by
    refine Finsupp.sum_congr fun w hw => ?_
    congr 1
    exact prox_transport σ (x v₀) (x w) (evalVec s v₀) (evalVec s w) hx₀ (hxB' w hw) (ν : ↥L → ℝ) hσ
  have hsupx : (⨆ i, (ν (x v₀ i) : ℝ)) = ⨆ i, ‖σ (evalVec s v₀ i)‖ := iSup_congr fun i => by rw [hσ, hx₀]
  have hval : (ν a : ℝ) = ‖σ (regVal s v₀ t k (B v₀).toNat u)‖ := by rw [hσ, ha]
  have hsupc : (⨆ φ, (ν (cL φ) : ℝ)) = ⨆ φ, ‖σ ((cL φ : ↥L) : AlgebraicClosure ℚ)‖ := iSup_congr fun φ => by rw [hσ]
  rw [hsum, hsupx, hval, hsupc]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold genFun at hgen
  by_cases hpos : 0 < B v₀
  · have hysup : (⨆ q, (ν (y q) : ℝ)) = ⨆ q : Fin r × Fin r,
        ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖ :=
      iSup_congr fun q => by rw [hσ, hy hpos q]
    rw [hysup]
    nlinarith [hgen, hdrop', hk0, hl2]
  · have h0 : B v₀ = 0 := le_antisymm (not_lt.mp hpos) (hBnn v₀)
    rw [h0] at hgen ⊢
    push_cast at hgen ⊢
    simp only [mul_zero, zero_mul, add_zero, sub_zero] at hgen ⊢
    nlinarith [hgen, hdrop', hk0, hl2]

end P2MJAU
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.P2MW"

open AlgebraicCurve ModularCurve

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
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
            + c₀ * k :=
  P2MJAU.main N s hs

end S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal (solution)
