-- Prove2me | solution 1 for ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/472c2396-6a2a-5b09-b5df-334a70cf2bd1

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_pointHt_mul_eq_add
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_ModularCurve_constantsAreBase_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_MvPolynomial_abv_eval_div_sub_eval_div_le
import Theorems.Thm_ModularCurve_exists_isHomogeneous_mul_aeval_eq_aeval_and_secVal_ne_zero
import Theorems.Thm_IsNonarchimedean_abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_one_le_abv_evalAt_of_le_prox
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MS4

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem exists_forall_ord_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem evalVec_apply (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]
  simp only [dif_pos hr]

end Pivot

section AbsHeight

end AbsHeight

section Eval

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem evalAt_add_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem smul_mem_of_mem (v : Place (AlgebraicClosure ℚ) F) (a : AlgebraicClosure ℚ) {f : F}
    (hf : f ∈ v.toValuationSubring) : a • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    (a : AlgebraicClosure ℚ) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

theorem sum_smul_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (c : ι → AlgebraicClosure ℚ) {f : ι → F} (hf : ∀ i, f i ∈ v.toValuationSubring) :
    (∑ i ∈ S, c i • f i) ∈ v.toValuationSubring :=
  sum_mem fun i _ => smul_mem_of_mem v (c i) (hf i)

theorem evalAt_sum_smul_of_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (hv : v.IsRational) (c : ι → AlgebraicClosure ℚ) {f : ι → F}
    (hf : ∀ i, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (v.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem v hv (smul_mem_of_mem v _ (hf a)) (sum_smul_mem S v c hf),
      evalAt_smul_of_mem v hv _ (hf a), ih]

end Eval

section Linear

end Linear

section Orders

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem ord_pivot_eq {r : ℕ} (hr : 0 < r) (f : Fin r → F) (hf : ∀ i, f i ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hfD : ∀ i, f i ∈ riemannRochSpace D)
    (v : Place (AlgebraicClosure ℚ) F) (hex : ∃ i, v.ord (f i) + D v = 0) :
    v.ord (f (pivotIndex f v hr)) = -D v := by
  obtain ⟨i, hi⟩ := hex
  apply le_antisymm
  · have := ord_pivot_le hr f v i; linarith
  · have := (mem_riemannRochSpace_iff.mp (hfD _) v).resolve_left (hf (pivotIndex f v hr)); linarith

end Orders

section EasyLin

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {a b : ℕ}

end EasyLin

section RRGeneric

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

theorem exists_index_notMem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (w : Place K F)
    (h : ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    ∃ i, x i ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  by_contra hall
  push Not at hall
  obtain ⟨f, hf, hf'⟩ := h
  apply hf'
  have hle : Submodule.span K (Set.range x) ≤ riemannRochSpace (D - Finsupp.single w 1) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  exact hle (hspan ▸ hf)

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

end RRGeneric

section Families

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

end Families

section Bar

variable (N : ℕ) [NeZero N]

theorem ell_eq_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hCD : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
    hasCanonicalDivisor_modularFunctionFieldBar N
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

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

theorem exists_mem_notMem_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
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

theorem bpf_of_span_eq {ι : Type*} (x : ι → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (x i) + D w = 0 := by
  intro w
  obtain ⟨i, hi⟩ := exists_index_notMem_of_span_eq x hspan w (exists_mem_notMem_bar N D hD w)
  exact ⟨i, ord_eq_of_mem_notMem w (mem_of_span_eq x hspan i) hi⟩

end Bar

end P2MS4

namespace P2MS4

section Chord

variable {N : ℕ} [NeZero N]

theorem degree_embDivisor : (embDivisor N).degree = (embDegree N : ℤ) := by
  rw [ModularCurve.embDivisor, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N]
  simp

theorem two_g_le_degree_embDivisor :
    2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
  rw [degree_embDivisor, ModularCurve.embDegree]; push_cast; omega

variable {r : ℕ}

theorem emb_ne_zero {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

theorem emb_mem {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r) : s i ∈ riemannRochSpace (embDivisor N) :=
  mem_of_span_eq s hs.2 i

theorem emb_bpf {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (s i) + embDivisor N w = 0 :=
  bpf_of_span_eq N s hs.2 two_g_le_degree_embDivisor

theorem ord_emb_pivot (hr : 0 < r) {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    w.ord (s (pivotIndex s w hr)) = -embDivisor N w :=
  ord_pivot_eq hr s (emb_ne_zero hs) (embDivisor N) (emb_mem hs) w (emb_bpf hs w)

end Chord

end P2MS4

namespace P2MS4

section ProjAt

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

variable (hr : 0 < r) {s : Fin r → F} (hs0 : ∀ i, s i ≠ 0) (hli : LinearIndependent (AlgebraicClosure ℚ) s)

variable {D : Divisor (AlgebraicClosure ℚ) F}
  (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
  (hbpf : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + D w = 0)
  (hrat : ∀ v : Place (AlgebraicClosure ℚ) F, v.IsRational)

theorem evalAt_eq_zero_iff_ord_pos (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    v.evalAt f = 0 ↔ 0 < v.ord f := by
  constructor
  · intro h0
    by_contra hle
    have h0' : v.ord f = 0 :=
      le_antisymm (not_lt.mp hle)
        (((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0)
    exact v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h0' h0
  · intro hpos
    have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
      rintro ⟨u, hu⟩
      have h := v.ord_coe_unit u
      rw [hu] at h
      change v.ord f = 0 at h
      omega
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
      by_contra h
      exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
    rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap (AlgebraicClosure ℚ) v.ResidueField),
      v.residueInv_algebraMap]

end ProjAt

end P2MS4

namespace P2MS4

section Core

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem card_emb_eq {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) :
    (r : ℤ) = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 2 := by
  have h1 : Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace (embDivisor N)) = r := by
    rw [← hs.2, finrank_span_eq_card hs.1, Fintype.card_fin]
  have h2 := ell_eq_bar N (embDivisor N)
    (by rw [degree_embDivisor, ModularCurve.embDegree]; push_cast; omega)
  have h3 : (ell (embDivisor N) : ℤ) = r := by unfold ell LSpace; exact_mod_cast h1
  rw [degree_embDivisor, ModularCurve.embDegree] at h2
  push_cast at h2
  omega

theorem two_le_card_emb {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) : 2 ≤ r := by
  have := card_emb_eq hs; omega

end Core

end P2MS4

namespace P2MSV

open P2MS4

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem secVal_apply (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (k : ℕ) (u : modularFunctionFieldBar N) :
    secVal s v k u = v.evalAt (u * (s (pivotIndex s v hr))⁻¹ ^ k) := by
  unfold secVal; rw [dif_pos hr]

variable {s : Fin r → modularFunctionFieldBar N}

theorem evalAt_pow_of_mem (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hR : R.IsRational) {f : modularFunctionFieldBar N} (hf : f ∈ R.toValuationSubring) :
    ∀ n : ℕ, R.evalAt (f ^ n) = R.evalAt f ^ n
  | 0 => by rw [pow_zero, pow_zero, Place.evalAt_one]
  | n + 1 => by rw [pow_succ, pow_succ, R.evalAt_mul_of_mem hR (Subring.pow_mem _ hf _) hf, evalAt_pow_of_mem R hR hf n]

theorem evalAt_prod_pow (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hR : R.IsRational) (f : Fin r → modularFunctionFieldBar N)
    (hf : ∀ i, f i ∈ R.toValuationSubring) (e : Fin r → ℕ) (S : Finset (Fin r)) :
    (∏ i ∈ S, f i ^ e i) ∈ R.toValuationSubring ∧
      R.evalAt (∏ i ∈ S, f i ^ e i) = ∏ i ∈ S, R.evalAt (f i) ^ e i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Place.evalAt_one, Subring.one_mem]
  | insert a S ha ih =>
    obtain ⟨hmem, hval⟩ := ih
    have hpow : f a ^ e a ∈ R.toValuationSubring := Subring.pow_mem _ (hf a) _
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨Subring.mul_mem _ hpow hmem, ?_⟩
    rw [R.evalAt_mul_of_mem hR hpow hmem, hval, evalAt_pow_of_mem R hR (hf a)]

theorem evalAt_finsuppProd (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hR : R.IsRational) (f : Fin r → modularFunctionFieldBar N)
    (hf : ∀ i, f i ∈ R.toValuationSubring) (m : Fin r →₀ ℕ) :
    (m.prod fun i e => f i ^ e) ∈ R.toValuationSubring ∧
      R.evalAt (m.prod fun i e => f i ^ e) = m.prod fun i e => R.evalAt (f i) ^ e :=
  evalAt_prod_pow R hR f hf m m.support

theorem monomial_mul_inv_pow (hr : 0 < r) (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (m : Fin r →₀ ℕ) {k : ℕ}
    (hm : m.degree = k) :
    (m.prod fun i e => s i ^ e) * (s (pivotIndex s R hr))⁻¹ ^ k
      = m.prod fun i e => (s i * (s (pivotIndex s R hr))⁻¹) ^ e := by
  classical
  show (∏ i ∈ m.support, s i ^ m i) * (s (pivotIndex s R hr))⁻¹ ^ k = ∏ i ∈ m.support, (s i * (s (pivotIndex s R hr))⁻¹) ^ m i
  have hk : k = ∑ i ∈ m.support, m i := by rw [← hm]; rfl
  rw [hk, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (mul_pow _ _ _).symm

theorem secVal_aeval (hs : IsEmbBasis N s) (hr : 0 < r) (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {k : ℕ}
    {P : MvPolynomial (Fin r) (AlgebraicClosure ℚ)} (hP : P.IsHomogeneous k) :
    MvPolynomial.aeval s P * (s (pivotIndex s R hr))⁻¹ ^ k ∈ R.toValuationSubring ∧
      secVal s R k (MvPolynomial.aeval s P) = MvPolynomial.eval (evalVec s R) P := by
  classical
  have hrat := isRational_bar N R
  have hs0 := emb_ne_zero hs
  set piv := s (pivotIndex s R hr) with hpiv
  have hpiv0 : piv ≠ 0 := hs0 _
  have hreg : ∀ i, s i * piv⁻¹ ∈ R.toValuationSubring := fun i => by
    refine R.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero hpiv0)) ?_
    rw [Place.ord_mul _ (hs0 i) (inv_ne_zero hpiv0), Place.ord_inv, hpiv, ord_emb_pivot hr hs R]
    have := ((mem_riemannRochSpace_iff.mp (emb_mem hs i)) R).resolve_left (hs0 i)
    linarith
  have hx : ∀ i, R.evalAt (s i * piv⁻¹) = evalVec s R i := fun i => by rw [evalVec_apply hr]

  have hexp : MvPolynomial.aeval s P * piv⁻¹ ^ k
      = ∑ m ∈ P.support, P.coeff m • (m.prod fun i e => (s i * piv⁻¹) ^ e) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hdeg : m.degree = k := by
      by_contra h; exact (MvPolynomial.mem_support_iff.mp hm) (hP.coeff_eq_zero h)
    rw [MvPolynomial.aeval_monomial, Algebra.smul_def, mul_assoc, monomial_mul_inv_pow hr R m hdeg]
  have hterm : ∀ m : Fin r →₀ ℕ, (m.prod fun i e => (s i * piv⁻¹) ^ e) ∈ R.toValuationSubring :=
    fun m => (evalAt_finsuppProd R hrat _ hreg m).1
  refine ⟨?_, ?_⟩
  · rw [hexp]
    exact Subring.sum_mem _ fun m _ => by
      rw [Algebra.smul_def]; exact Subring.mul_mem _ (R.algebraMap_mem' _) (hterm m)
  · rw [secVal_apply hr, ← hpiv, hexp, evalAt_sum_smul_of_mem P.support R hrat (fun m => P.coeff m) hterm,
      MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [(evalAt_finsuppProd R hrat _ hreg m).2]
    unfold Finsupp.prod
    congr 1
    exact Finset.prod_congr rfl fun i _ => by show R.evalAt (s i * piv⁻¹) ^ m i = _; rw [hx i]

theorem evalAt_eq_eval_div_eval (hs : IsEmbBasis N s) (hr : 0 < r) (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {k : ℕ}
    {A B : MvPolynomial (Fin r) (AlgebraicClosure ℚ)} (hA : A.IsHomogeneous k) (hB : B.IsHomogeneous k)
    {h : modularFunctionFieldBar N} (hh : h ∈ R.toValuationSubring) (hAB : h * MvPolynomial.aeval s B = MvPolynomial.aeval s A)
    (hBx : MvPolynomial.eval (evalVec s R) B ≠ 0) :
    R.evalAt h = MvPolynomial.eval (evalVec s R) A / MvPolynomial.eval (evalVec s R) B := by
  have hrat := isRational_bar N R
  obtain ⟨hBmem, hBval⟩ := secVal_aeval hs hr R hB
  obtain ⟨-, hAval⟩ := secVal_aeval hs hr R hA
  rw [secVal_apply hr] at hAval hBval
  have e : MvPolynomial.aeval s A * (s (pivotIndex s R hr))⁻¹ ^ k
      = h * (MvPolynomial.aeval s B * (s (pivotIndex s R hr))⁻¹ ^ k) := by rw [← hAB]; ring
  rw [e, R.evalAt_mul_of_mem hrat hh hBmem, hBval] at hAval
  rw [eq_div_iff hBx, hAval]

end P2MSV

namespace P2MC24C

open P2MS4

section Generic

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {n : ℕ}

theorem eval_smul_of_isHomogeneous {φ : MvPolynomial (Fin n) K} {k : ℕ} (hφ : φ.IsHomogeneous k)
    (t : K) (x : Fin n → K) : MvPolynomial.eval (t • x) φ = t ^ k * MvPolynomial.eval x φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = k := by
    have : m.degree = k := by
      by_contra h; exact (MvPolynomial.mem_support_iff.mp hm) (hφ.coeff_eq_zero h)
    rw [← this]; rfl
  have e : ∏ i ∈ m.support, (t • x) i ^ m i = t ^ k * ∏ i ∈ m.support, x i ^ m i := by
    rw [← hdeg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [e]; ring

theorem exists_max_index (hn : 0 < n) (x : Fin n → K) : ∃ i : Fin n, ∀ l, μ (x l) ≤ μ (x i) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun l => μ (x l)) Finset.univ_nonempty
  exact ⟨i, fun l => hi l (Finset.mem_univ l)⟩

theorem iSup_abv_eq_one (x : Fin n → K) (i : Fin n) (hxi : x i = 1) (hx : ∀ l, μ (x l) ≤ 1) :
    (⨆ l, μ (x l)) = 1 := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  apply le_antisymm (ciSup_le hx)
  calc (1 : ℝ) = μ (x i) := by rw [hxi, map_one]
    _ ≤ ⨆ l, μ (x l) := le_ciSup (Finite.bddAbove_range fun l => μ (x l)) i

theorem prox_eq_neg_log_iSup_minors (x v : Fin n → K) (i j : Fin n) (hxi : x i = 1) (hvj : v j = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    prox μ x v = -Real.log (⨆ q : Fin n × Fin n, μ (x q.1 * v q.2 - x q.2 * v q.1)) := by
  rw [prox, iSup_abv_eq_one μ x i hxi hx, iSup_abv_eq_one μ v j hvj hv, Real.log_one]
  ring

theorem le_iSup_minors (x v : Fin n → K) (l m : Fin n) :
    μ (x l * v m - x m * v l) ≤ ⨆ q : Fin n × Fin n, μ (x q.1 * v q.2 - x q.2 * v q.1) :=
  le_ciSup (f := fun q : Fin n × Fin n => μ (x q.1 * v q.2 - x q.2 * v q.1)) (Finite.bddAbove_range _) (l, m)

theorem iSup_minors_nonneg (x v : Fin n → K) : 0 ≤ ⨆ q : Fin n × Fin n, μ (x q.1 * v q.2 - x q.2 * v q.1) :=
  Real.iSup_nonneg fun _ => apply_nonneg _ _

theorem eq_smul_of_iSup_minors_eq_zero (x v : Fin n → K) (j : Fin n) (hvj : v j ≠ 0)
    (h0 : (⨆ q : Fin n × Fin n, μ (x q.1 * v q.2 - x q.2 * v q.1)) = 0) : x = (x j / v j) • v := by
  funext l
  have hz : μ (x l * v j - x j * v l) = 0 := le_antisymm (h0 ▸ le_iSup_minors μ x v l j) (apply_nonneg _ _)
  rw [AbsoluteValue.eq_zero] at hz
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hz

theorem norm_row (x : Fin n → K) (i : Fin n) (hmax : ∀ l, μ (x l) ≤ μ (x i)) (hxi : x i ≠ 0) :
    ((x i)⁻¹ • x) i = 1 ∧ ∀ l, μ (((x i)⁻¹ • x) l) ≤ 1 := by
  refine ⟨by rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hxi], fun l => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  have hpos : 0 < μ (x i) := μ.pos hxi
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact hmax l

theorem exp_bounds_of_abs_log_le {a b : ℝ} (ha : 0 < a) (h : |Real.log a| ≤ b) :
    Real.exp (-b) ≤ a ∧ a ≤ Real.exp b := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor
  · calc Real.exp (-b) ≤ Real.exp (Real.log a) := Real.exp_le_exp.mpr h1
      _ = a := Real.exp_log ha
  · calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp b := Real.exp_le_exp.mpr h2

theorem abv_add_eq_of_lt (hμ : IsNonarchimedean μ) {a b : K} (h : μ a < μ b) : μ (a + b) = μ b := by
  apply le_antisymm ((hμ a b).trans (max_le h.le le_rfl))
  have h1 : μ b ≤ max (μ (a + b)) (μ a) := by
    have := hμ (a + b) (-a)
    rwa [add_neg_cancel_comm, μ.map_neg] at this
  rcases le_max_iff.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (not_le.mpr h)

end Generic

theorem exists_const (β : AlgebraicClosure ℚ) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ → μ (p : AlgebraicClosure ℚ) < 1 →
      |Real.log (μ β)| ≤ c * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  by_cases hβ : β = 0
  · refine ⟨0, le_rfl, fun μ _ _ => ?_⟩
    rw [hβ, map_zero, Real.log_zero, abs_zero, zero_mul]
  · exact exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic β hβ ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic β) p hp

section Core

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem core {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (h : modularFunctionFieldBar N) (hh : h ≠ 0)
    (Q' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ : h ∈ Q'.toValuationSubring) (p : ℕ) (hp : p.Prime) :
    ∃ c ch : ℝ, 0 ≤ c ∧ 0 ≤ ch ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ → μ (p : AlgebraicClosure ℚ) < 1 →
        |Real.log (μ (Q'.evalAt h))| ≤ ch * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ → μ (p : AlgebraicClosure ℚ) < 1 →
        ∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), h ∈ R.toValuationSubring →
          c * (-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ prox μ (evalVec s R) (evalVec s Q') →
          μ (R.evalAt h - Q'.evalAt h) < Real.exp (-((1 + ch) * (-Real.log (μ (p : AlgebraicClosure ℚ))))) := by
  classical

  have h2 : 2 ≤ r := two_le_card_emb hs
  have hr : 0 < r := by omega
  have hs0 := emb_ne_zero hs
  have hratQ := isRational_bar N Q'
  set x₀ := evalVec s Q' with hx₀
  have hx₀piv : x₀ (pivotIndex s Q' hr) = 1 := by
    rw [hx₀, evalVec_apply hr, mul_inv_cancel₀ (hs0 _), Place.evalAt_one]
  have hx₀0 : x₀ ≠ 0 := fun h0 => by have := congrFun h0 (pivotIndex s Q' hr); rw [hx₀piv] at this; exact one_ne_zero this

  obtain ⟨k, A, B, hk1, hA, hB, hAB, hBsec⟩ :=
    ModularCurve.exists_isHomogeneous_mul_aeval_eq_aeval_and_secVal_ne_zero N s hs h Q' hQ
  have hB0 : MvPolynomial.eval x₀ B ≠ 0 := by rw [hx₀, ← (P2MSV.secVal_aeval hs hr Q' hB).2]; exact hBsec
  have hvalQ : Q'.evalAt h = MvPolynomial.eval x₀ A / MvPolynomial.eval x₀ B :=
    P2MSV.evalAt_eq_eval_div_eval hs hr Q' hA hB hQ hAB hB0

  choose cst hcst0 hcst using fun β : AlgebraicClosure ℚ => exists_const β p hp
  set cA : ℝ := ∑ m ∈ A.support, cst (A.coeff m) with hcA
  set cB : ℝ := ∑ m ∈ B.support, cst (B.coeff m) with hcB
  set cX : ℝ := ∑ l, cst (x₀ l) with hcX
  set c3 : ℝ := cst (MvPolynomial.eval x₀ B) with hc3
  set c4 : ℝ := cst (Q'.evalAt h) with hc4
  set c5 : ℝ := cst (MvPolynomial.eval x₀ A) with hc5
  have hcA0 : 0 ≤ cA := Finset.sum_nonneg fun m _ => hcst0 _
  have hcB0 : 0 ≤ cB := Finset.sum_nonneg fun m _ => hcst0 _
  have hcX0 : 0 ≤ cX := Finset.sum_nonneg fun l _ => hcst0 _
  have hc30 : 0 ≤ c3 := hcst0 _
  have hc40 : 0 ≤ c4 := hcst0 _
  have hc50 : 0 ≤ c5 := hcst0 _
  set c : ℝ := 2 + c4 + cA + cB + c5 + 3 * c3 + 3 * k * cX with hc
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkc : 0 ≤ (k : ℝ) * cX := mul_nonneg hk0 hcX0
  refine ⟨c, c4, by positivity, hc40, fun μ hμ hμp => hcst _ μ hμ hμp, ?_⟩
  intro μ hμ hμp R hR hprox

  have hp0 : (0 : ℝ) < μ (p : AlgebraicClosure ℚ) := μ.pos (Nat.cast_ne_zero.mpr hp.ne_zero)
  set L : ℝ := -Real.log (μ (p : AlgebraicClosure ℚ)) with hL
  have hLpos : 0 < L := by rw [hL, neg_pos]; exact Real.log_neg hp0 hμp

  have hup : ∀ β : AlgebraicClosure ℚ, μ β ≤ Real.exp (cst β * L) := by
    intro β
    by_cases hβ : β = 0
    · rw [hβ, map_zero]; exact (Real.exp_pos _).le
    · exact (exp_bounds_of_abs_log_le (μ.pos hβ) (hcst β μ hμ hμp)).2
  have hlow : ∀ β : AlgebraicClosure ℚ, β ≠ 0 → Real.exp (-(cst β * L)) ≤ μ β := fun β hβ =>
    (exp_bounds_of_abs_log_le (μ.pos hβ) (hcst β μ hμ hμp)).1

  have hcoefA : ∀ m, μ (A.coeff m) ≤ Real.exp (cA * L) := by
    intro m
    by_cases hm : m ∈ A.support
    · refine (hup _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hLpos.le))
      exact Finset.single_le_sum (fun m _ => hcst0 (A.coeff m)) hm
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]; exact (Real.exp_pos _).le
  have hcoefB : ∀ m, μ (B.coeff m) ≤ Real.exp (cB * L) := by
    intro m
    by_cases hm : m ∈ B.support
    · refine (hup _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hLpos.le))
      exact Finset.single_le_sum (fun m _ => hcst0 (B.coeff m)) hm
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]; exact (Real.exp_pos _).le

  have hx₀up : ∀ l, μ (x₀ l) ≤ Real.exp (cX * L) := fun l =>
    (hup _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun l _ => hcst0 (x₀ l)) (Finset.mem_univ l)) hLpos.le))

  set xR := evalVec s R with hxR
  have hratR := isRational_bar N R
  have hxRpiv : xR (pivotIndex s R hr) = 1 := by
    rw [hxR, evalVec_apply hr, mul_inv_cancel₀ (hs0 _), Place.evalAt_one]
  have hxR0 : xR ≠ 0 := fun h0 => by have := congrFun h0 (pivotIndex s R hr); rw [hxRpiv] at this; exact one_ne_zero this

  set M : ℝ := ⨆ q : Fin r × Fin r, μ (xR q.1 * x₀ q.2 - xR q.2 * x₀ q.1) with hM
  by_cases hM0 : M = 0
  ·
    have hprop := eq_smul_of_iSup_minors_eq_zero μ xR x₀ (pivotIndex s Q' hr) (by rw [hx₀piv]; exact one_ne_zero) hM0
    set t := xR (pivotIndex s Q' hr) / x₀ (pivotIndex s Q' hr) with ht
    have ht0 : t ≠ 0 := fun h0 => hxR0 (by rw [hprop, h0, zero_smul])
    have hBR : MvPolynomial.eval xR B ≠ 0 := by
      rw [hprop, eval_smul_of_isHomogeneous hB]; exact mul_ne_zero (pow_ne_zero _ ht0) hB0
    have hvalR : R.evalAt h = MvPolynomial.eval xR A / MvPolynomial.eval xR B :=
      P2MSV.evalAt_eq_eval_div_eval hs hr R hA hB hR hAB hBR
    have heq : R.evalAt h = Q'.evalAt h := by
      rw [hvalR, hvalQ, hprop, eval_smul_of_isHomogeneous hA, eval_smul_of_isHomogeneous hB,
        mul_div_mul_left _ _ (pow_ne_zero _ ht0)]
    rw [heq, sub_self, map_zero]; exact Real.exp_pos _

  have hMpos : 0 < M := lt_of_le_of_ne (iSup_minors_nonneg μ xR x₀) (Ne.symm hM0)

  obtain ⟨iR, hiR⟩ := exists_max_index μ hr xR
  obtain ⟨iQ, hiQ⟩ := exists_max_index μ hr x₀
  have hxRi : xR iR ≠ 0 := fun h0 => by
    have := hiR (pivotIndex s R hr); rw [hxRpiv, h0, map_zero, map_one] at this; linarith
  have hx₀i : x₀ iQ ≠ 0 := fun h0 => by
    have := hiQ (pivotIndex s Q' hr); rw [hx₀piv, h0, map_zero, map_one] at this; linarith
  set xh := (xR iR)⁻¹ • xR with hxh
  set vh := (x₀ iQ)⁻¹ • x₀ with hvh
  obtain ⟨hxh1, hxhint⟩ := norm_row μ xR iR hiR hxRi
  obtain ⟨hvh1, hvhint⟩ := norm_row μ x₀ iQ hiQ hx₀i
  rw [← hxh] at hxh1 hxhint
  rw [← hvh] at hvh1 hvhint

  have hx₀iQ1 : 1 ≤ μ (x₀ iQ) := by have := hiQ (pivotIndex s Q' hr); rwa [hx₀piv, map_one] at this
  have hτle : μ ((x₀ iQ)⁻¹) ≤ 1 := by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hx₀iQ1
  have hτge : Real.exp (-(cX * L)) ≤ μ ((x₀ iQ)⁻¹) := by
    rw [map_inv₀, Real.exp_neg]
    exact inv_anti₀ (lt_of_lt_of_le one_pos hx₀iQ1) (hx₀up iQ)

  have hprox1 : prox μ xh vh = prox μ xR x₀ := by
    rw [hxh, hvh]; exact AlgebraicCurve.prox_smul_smul μ xR x₀ (inv_ne_zero hxRi) (inv_ne_zero hx₀i) hM0
  set Mh : ℝ := ⨆ q : Fin r × Fin r, μ (xh q.1 * vh q.2 - xh q.2 * vh q.1) with hMh
  have hproxMh : prox μ xh vh = -Real.log Mh := prox_eq_neg_log_iSup_minors μ xh vh iR iQ hxh1 hvh1 hxhint hvhint
  have hcL : c * L ≤ -Real.log Mh := by rw [← hproxMh, hprox1]; exact hprox
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  have hcLpos : 0 < c * L := mul_pos (by linarith) hLpos
  have hMh0 : Mh ≠ 0 := fun h0 => by rw [h0, Real.log_zero, neg_zero] at hcL; linarith
  have hMhpos : 0 < Mh := lt_of_le_of_ne (iSup_minors_nonneg μ xh vh) (Ne.symm hMh0)
  have hMhle : Mh ≤ Real.exp (-(c * L)) := by
    have : Real.log Mh ≤ -(c * L) := by linarith
    calc Mh = Real.exp (Real.log Mh) := (Real.exp_log hMhpos).symm
      _ ≤ Real.exp (-(c * L)) := Real.exp_le_exp.mpr this
  have hMhlt1 : Mh < 1 := lt_of_le_of_lt hMhle (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith))

  have hvhiR : μ (vh iR) = 1 :=
    IsNonarchimedean.abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one μ hμ xh vh hxhint hvhint
      ⟨iQ, by rw [hvh1, map_one]⟩ hMhlt1 iR (by rw [hxh1, map_one])
  have hvhiR0 : vh iR ≠ 0 := fun h0 => by rw [h0, map_zero] at hvhiR; exact zero_ne_one hvhiR

  set vh' := (vh iR)⁻¹ • vh with hvh'
  have hvh'1 : vh' iR = 1 := by rw [hvh', Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hvhiR0]
  have hvh'int : ∀ l, μ (vh' l) ≤ 1 := fun l => by
    rw [hvh', Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, hvhiR, inv_one, one_mul]; exact hvhint l
  have hprox2 : prox μ xh vh' = prox μ xh vh := by
    have := AlgebraicCurve.prox_smul_smul μ xh vh one_ne_zero (inv_ne_zero hvhiR0) hMh0
    rwa [one_smul, ← hvh'] at this

  set D : ℝ := ⨆ l, μ (xh l - vh' l) with hD
  have hproxD : prox μ xh vh' = -Real.log D :=
    AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ xh vh' iR hxh1 hvh'1 hxhint hvh'int
  have hcLD : c * L ≤ -Real.log D := by rw [← hproxD, hprox2, hprox1]; exact hprox
  have hD0 : 0 ≤ D := Real.iSup_nonneg fun _ => apply_nonneg _ _
  have hDle : D ≤ Real.exp (-(c * L)) := by
    rcases hD0.lt_or_eq with hDpos | hDz
    · have : Real.log D ≤ -(c * L) := by linarith
      calc D = Real.exp (Real.log D) := (Real.exp_log hDpos).symm
        _ ≤ Real.exp (-(c * L)) := Real.exp_le_exp.mpr this
    · rw [← hDz]; exact (Real.exp_pos _).le

  set σ : AlgebraicClosure ℚ := (vh iR)⁻¹ * (x₀ iQ)⁻¹ with hσ
  have hvh'x₀ : vh' = σ • x₀ := by rw [hvh', hvh, smul_smul]
  have hσ0 : σ ≠ 0 := mul_ne_zero (inv_ne_zero hvhiR0) (inv_ne_zero hx₀i)
  have hμσ : μ σ = μ ((x₀ iQ)⁻¹) := by rw [hσ, map_mul, map_inv₀, hvhiR, inv_one, one_mul]
  have hBv' : MvPolynomial.eval vh' B = σ ^ k * MvPolynomial.eval x₀ B := by rw [hvh'x₀, eval_smul_of_isHomogeneous hB]
  have hAv' : MvPolynomial.eval vh' A = σ ^ k * MvPolynomial.eval x₀ A := by rw [hvh'x₀, eval_smul_of_isHomogeneous hA]
  have hBv'0 : MvPolynomial.eval vh' B ≠ 0 := by rw [hBv']; exact mul_ne_zero (pow_ne_zero _ hσ0) hB0

  have hμBv'low : Real.exp (-((k * cX + c3) * L)) ≤ μ (MvPolynomial.eval vh' B) := by
    rw [hBv', map_mul, map_pow, hμσ, show -((k * cX + c3) * L) = k * (-(cX * L)) + (-(c3 * L)) by ring,
      Real.exp_add, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le hτge k) (hlow _ hB0) (Real.exp_pos _).le
      (pow_nonneg (apply_nonneg _ _) _)
  have hμBv'up : μ (MvPolynomial.eval vh' B) ≤ Real.exp (c3 * L) := by
    rw [hBv', map_mul, map_pow, hμσ]
    calc μ ((x₀ iQ)⁻¹) ^ k * μ (MvPolynomial.eval x₀ B) ≤ 1 ^ k * Real.exp (c3 * L) :=
          mul_le_mul (pow_le_pow_left₀ (apply_nonneg _ _) hτle k) (hup _) (apply_nonneg _ _) (by positivity)
      _ = Real.exp (c3 * L) := by rw [one_pow, one_mul]
  have hμAv'up : μ (MvPolynomial.eval vh' A) ≤ Real.exp (c5 * L) := by
    rw [hAv', map_mul, map_pow, hμσ]
    calc μ ((x₀ iQ)⁻¹) ^ k * μ (MvPolynomial.eval x₀ A) ≤ 1 ^ k * Real.exp (c5 * L) :=
          mul_le_mul (pow_le_pow_left₀ (apply_nonneg _ _) hτle k) (hup _) (apply_nonneg _ _) (by positivity)
      _ = Real.exp (c5 * L) := by rw [one_pow, one_mul]

  have hclose : Real.exp (cB * L) * D < μ (MvPolynomial.eval vh' B) := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hDle (Real.exp_pos _).le) (lt_of_lt_of_le ?_ hμBv'low)
    rw [← Real.exp_add, Real.exp_lt_exp]
    have h1 : cB + (k * cX + c3) < c := by rw [hc]; linarith
    have h2 := mul_lt_mul_of_pos_right h1 hLpos
    linarith
  obtain ⟨hBxh, hquot⟩ := MvPolynomial.abv_eval_div_sub_eval_div_le μ hμ A B (Real.exp (cA * L)) (Real.exp (cB * L))
    hcoefA hcoefB xh vh' hxhint hvh'int hBv'0 hclose

  have hBxh0 : MvPolynomial.eval xh B ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hBxh; exact (μ.pos hBv'0).ne hBxh
  have hBR : MvPolynomial.eval xR B ≠ 0 := by
    intro h0; apply hBxh0; rw [hxh, eval_smul_of_isHomogeneous hB, h0, mul_zero]
  have hvalR : R.evalAt h = MvPolynomial.eval xh A / MvPolynomial.eval xh B := by
    rw [P2MSV.evalAt_eq_eval_div_eval hs hr R hA hB hR hAB hBR, hxh, eval_smul_of_isHomogeneous hA,
      eval_smul_of_isHomogeneous hB, mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero hxRi))]
  have hvalQ' : Q'.evalAt h = MvPolynomial.eval vh' A / MvPolynomial.eval vh' B := by
    rw [hvalQ, hAv', hBv', mul_div_mul_left _ _ (pow_ne_zero _ hσ0)]
  rw [hvalR, hvalQ']
  refine lt_of_le_of_lt hquot ?_

  set E₁ : ℝ := cA + cB + c3 + c5 with hE₁
  set E₂ : ℝ := 2 * (k * cX + c3) with hE₂
  have hnum : max (Real.exp (cA * L) * μ (MvPolynomial.eval vh' B)) (Real.exp (cB * L) * μ (MvPolynomial.eval vh' A))
      ≤ Real.exp (E₁ * L) := by
    refine max_le ?_ ?_
    · calc Real.exp (cA * L) * μ (MvPolynomial.eval vh' B) ≤ Real.exp (cA * L) * Real.exp (c3 * L) :=
            mul_le_mul_of_nonneg_left hμBv'up (Real.exp_pos _).le
        _ = Real.exp ((cA + c3) * L) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (E₁ * L) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by rw [hE₁]; linarith) hLpos.le)
    · calc Real.exp (cB * L) * μ (MvPolynomial.eval vh' A) ≤ Real.exp (cB * L) * Real.exp (c5 * L) :=
            mul_le_mul_of_nonneg_left hμAv'up (Real.exp_pos _).le
        _ = Real.exp ((cB + c5) * L) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (E₁ * L) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by rw [hE₁]; linarith) hLpos.le)
  have hden : Real.exp (-(E₂ * L)) ≤ μ (MvPolynomial.eval vh' B) ^ 2 := by
    have := pow_le_pow_left₀ (Real.exp_pos _).le hμBv'low 2
    rwa [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -((k * cX + c3) * L) = -(E₂ * L) by rw [hE₂]; push_cast; ring] at this
  have hκ : max (Real.exp (cA * L) * μ (MvPolynomial.eval vh' B)) (Real.exp (cB * L) * μ (MvPolynomial.eval vh' A))
      / μ (MvPolynomial.eval vh' B) ^ 2 ≤ Real.exp ((E₁ + E₂) * L) := by
    calc _ ≤ Real.exp (E₁ * L) / μ (MvPolynomial.eval vh' B) ^ 2 :=
          div_le_div_of_nonneg_right hnum (pow_nonneg (apply_nonneg _ _) _)
      _ ≤ Real.exp (E₁ * L) / Real.exp (-(E₂ * L)) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hden
      _ = Real.exp ((E₁ + E₂) * L) := by rw [← Real.exp_sub]; ring_nf
  calc max (Real.exp (cA * L) * μ (MvPolynomial.eval vh' B)) (Real.exp (cB * L) * μ (MvPolynomial.eval vh' A))
        / μ (MvPolynomial.eval vh' B) ^ 2 * D
      ≤ Real.exp ((E₁ + E₂) * L) * Real.exp (-(c * L)) :=
        mul_le_mul hκ hDle hD0 (Real.exp_pos _).le
    _ = Real.exp ((E₁ + E₂ - c) * L) := by rw [← Real.exp_add]; ring_nf
    _ < Real.exp (-((1 + c4) * L)) := by
        rw [Real.exp_lt_exp]
        have h1 : E₁ + E₂ - c < -(1 + c4) := by rw [hE₁, hE₂, hc]; linarith
        have h2 := mul_lt_mul_of_pos_right h1 hLpos
        linarith

end Core

section Curve

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem stub_C24b_abv_evalAt_eq_of_prox_ge (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (h : modularFunctionFieldBar N)
    (Q' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ' : Q'.ord h = 0) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ → μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.ord h = 0 →
        c * (-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ prox μ (evalVec s R) (evalVec s Q') →
        μ (R.evalAt h) = μ (Q'.evalAt h) := by
  by_cases hh : h = 0
  · refine ⟨0, le_rfl, fun μ _ _ R _ _ => ?_⟩
    rw [hh, ← map_zero (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), Place.evalAt_algebraMap_eq, Place.evalAt_algebraMap_eq]
  have hQreg : h ∈ Q'.toValuationSubring := Q'.mem_toValuationSubring_of_ord_nonneg_alt hh hQ'.ge
  have hratQ := isRational_bar N Q'
  have hQval0 : Q'.evalAt h ≠ 0 := Q'.evalAt_ne_zero_of_ord_eq_zero hratQ hh hQ'
  obtain ⟨c, ch, hc0, hch0, hch, hcore⟩ := core hs h hh Q' hQreg p hp
  refine ⟨c, hc0, fun μ hμ hμp R hR hprox => ?_⟩
  have hRreg : h ∈ R.toValuationSubring := R.mem_toValuationSubring_of_ord_nonneg_alt hh hR.ge
  have hlt := hcore μ hμ hμp R hRreg hprox
  have hp0 : (0 : ℝ) < μ (p : AlgebraicClosure ℚ) := μ.pos (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hLpos : 0 < -Real.log (μ (p : AlgebraicClosure ℚ)) := by rw [neg_pos]; exact Real.log_neg hp0 hμp

  have hlow : Real.exp (-((1 + ch) * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ≤ μ (Q'.evalAt h) := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_bounds_of_abs_log_le (μ.pos hQval0) (hch μ hμ hμp)).1
    rw [neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right (by linarith) hLpos.le
  have := abv_add_eq_of_lt μ hμ (lt_of_lt_of_le hlt hlow)
  rwa [sub_add_cancel] at this

theorem stub_C24c_one_le_abv_evalAt_of_prox_ge (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (h : modularFunctionFieldBar N)
    (Q' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ' : Q'.ord h < 0) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ → μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.ord h = 0 →
        c * (-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ prox μ (evalVec s R) (evalVec s Q') →
        1 ≤ μ (R.evalAt h) := by
  have hh : h ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at hQ'; exact lt_irrefl _ hQ'
  set g : modularFunctionFieldBar N := h⁻¹ with hg
  have hg0 : g ≠ 0 := inv_ne_zero hh
  have hordQg : 0 < Q'.ord g := by rw [hg, Place.ord_inv]; linarith
  have hQreg : g ∈ Q'.toValuationSubring := Q'.mem_toValuationSubring_of_ord_nonneg_alt hg0 hordQg.le
  have hratQ := isRational_bar N Q'
  have hQval : Q'.evalAt g = 0 := (evalAt_eq_zero_iff_ord_pos Q' hratQ hQreg hg0).mpr hordQg
  obtain ⟨c, ch, hc0, hch0, -, hcore⟩ := core hs g hg0 Q' hQreg p hp
  refine ⟨c, hc0, fun μ hμ hμp R hR hprox => ?_⟩
  have hratR := isRational_bar N R
  have hordRg : R.ord g = 0 := by rw [hg, Place.ord_inv, hR, neg_zero]
  have hRg : g ∈ R.toValuationSubring := R.mem_toValuationSubring_of_ord_nonneg_alt hg0 hordRg.ge
  have hRh : h ∈ R.toValuationSubring := R.mem_toValuationSubring_of_ord_nonneg_alt hh hR.ge
  have hlt := hcore μ hμ hμp R hRg hprox
  rw [hQval, sub_zero] at hlt
  have hp0 : (0 : ℝ) < μ (p : AlgebraicClosure ℚ) := μ.pos (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hLpos : 0 < -Real.log (μ (p : AlgebraicClosure ℚ)) := by rw [neg_pos]; exact Real.log_neg hp0 hμp
  have hle1 : μ (R.evalAt g) ≤ 1 := by
    refine hlt.le.trans (Real.exp_le_one_iff.mpr ?_)
    rw [neg_nonpos]
    exact mul_nonneg (by linarith) hLpos.le
  have hgval0 : R.evalAt g ≠ 0 := R.evalAt_ne_zero_of_ord_eq_zero hratR hg0 hordRg
  have hgh : g * h = 1 := by rw [hg]; exact inv_mul_cancel₀ hh
  have hinv : R.evalAt h = (R.evalAt g)⁻¹ := by
    have hmul := R.evalAt_mul_of_mem hratR hRg hRh
    rw [hgh, Place.evalAt_one] at hmul
    exact eq_inv_of_mul_eq_one_right hmul.symm
  rw [hinv, map_inv₀]
  exact (one_le_inv₀ (μ.pos hgval0)).mpr hle1

end Curve

end P2MC24C

end

open AlgebraicCurve ModularCurve in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (h : modularFunctionFieldBar N)
    (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ : Q.ord h < 0) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.ord h = 0 →
        c * (-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ prox μ (evalVec s R) (evalVec s Q) →
        1 ≤ μ (R.evalAt h) :=
  P2MC24C.stub_C24c_one_le_abv_evalAt_of_prox_ge s hs h Q hQ p hp

end S_ModularCurve_JZero_exists_one_le_abv_evalAt_of_le_prox
end P2MW
export P2MW.S_ModularCurve_JZero_exists_one_le_abv_evalAt_of_le_prox (solution)
