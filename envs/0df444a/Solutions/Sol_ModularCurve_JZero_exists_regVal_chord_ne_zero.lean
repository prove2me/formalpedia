-- Prove2me | solution 1 for ModularCurve.JZero.exists_regVal_chord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a0000d1a-926b-5fc2-a2c8-234278990abb

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
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

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
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero.P2MW"

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
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero.P2MW"

namespace P2MYG

open AlgebraicCurve ModularCurve P2MW

noncomputable section

def chordFun {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (w₀ : Place (AlgebraicClosure ℚ) F) (p : Fin r × Fin r) : F :=
  evalVec s w₀ p.1 • s p.2 - evalVec s w₀ p.2 • s p.1

theorem ratio_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j))
    (i : Fin r) : s i * (s p)⁻¹ ∈ w.toValuationSubring :=
  w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 p)))
    (by rw [w.ord_mul (hs0 i) (inv_ne_zero (hs0 p)), w.ord_inv]; linarith [hp i])

section Bar

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
variable {N}

theorem degree_embDivisor : (embDivisor N).degree = embDegree N := by
  rw [embDivisor, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N]; simp

omit [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
theorem embDegree_cast : (embDegree N : ℤ) = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 := by
  rw [embDegree]; push_cast; ring

theorem chordFun_mem {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (p : Fin r × Fin r) :
    chordFun s o p ∈ riemannRochSpace (embDivisor N - Finsupp.single o 1) := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hr : 0 < r := pos_of_span_eq N s hs.2 (by rw [degree_embDivisor, embDegree_cast]; omega)
  have ho_rat := isRational_bar N o
  set piv := pivotIndex s o hr with hpiv
  have hp : ∀ j, o.ord (s piv) ≤ o.ord (s j) := ord_pivot_le N hr s o
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := mem_of_span_eq s hs.2

  have hmemE : chordFun s o p ∈ riemannRochSpace (embDivisor N) :=
    sub_mem (Submodule.smul_mem _ _ (hsmem p.2)) (Submodule.smul_mem _ _ (hsmem p.1))

  set fi := s p.1 * (s piv)⁻¹
  set fj := s p.2 * (s piv)⁻¹
  have hfi : fi ∈ o.toValuationSubring := ratio_mem N s hs0 o piv hp p.1
  have hfj : fj ∈ o.toValuationSubring := ratio_mem N s hs0 o piv hp p.2
  set g := evalVec s o p.1 • fj - evalVec s o p.2 • fi with hg
  have hgmem : g ∈ o.toValuationSubring := sub_mem (smul_mem_of_mem o _ hfj) (smul_mem_of_mem o _ hfi)
  have hfact : chordFun s o p = g * s piv := by
    simp only [chordFun, hg, sub_mul, smul_mul_assoc]
    rw [inv_mul_cancel_right₀ (hs0 piv), inv_mul_cancel_right₀ (hs0 piv)]
  have hgval : o.evalAt g = 0 := by
    rw [hg, evalAt_sub_of_mem o ho_rat (smul_mem_of_mem o _ hfj) (smul_mem_of_mem o _ hfi),
      evalAt_smul_of_mem o ho_rat _ hfj, evalAt_smul_of_mem o ho_rat _ hfi,
      evalVec_apply N hr s o p.1, evalVec_apply N hr s o p.2]
    ring
  rw [mem_riemannRochSpace_iff]
  intro w
  rcases eq_or_ne (chordFun s o p) 0 with h0 | h0
  · exact Or.inl h0
  right
  by_cases hw : w = o
  · subst w
    have hg0 : g ≠ 0 := by intro h; apply h0; rw [hfact, h, zero_mul]
    have hordg : 0 < o.ord g := ord_pos_of_evalAt_eq_zero _ ho_rat hg0 hgmem hgval
    have hordpiv : -embDivisor N o ≤ o.ord (s piv) :=
      ((mem_riemannRochSpace_iff.mp (hsmem piv)) _).resolve_left (hs0 piv)
    rw [hfact, Place.ord_mul _ hg0 (hs0 piv), Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]
    omega
  · have h1 := ((mem_riemannRochSpace_iff.mp hmemE) w).resolve_left h0
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hw), sub_zero]
    exact h1

theorem span_chordFun_eq {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Submodule.span (AlgebraicClosure ℚ) (Set.range (chordFun s o))
      = riemannRochSpace (embDivisor N - Finsupp.single o 1) := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]; omega
  have hr : 0 < r := pos_of_span_eq N s hs.2 hdegE
  have ho_rat := isRational_bar N o
  set piv := pivotIndex s o hr with hpiv
  have hp : ∀ j, o.ord (s piv) ≤ o.ord (s j) := ord_pivot_le N hr s o
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := mem_of_span_eq s hs.2
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact chordFun_mem s hs o p)
  · intro f hf
    have hfE : f ∈ riemannRochSpace (embDivisor N) := by
      refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_) hf
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    have hspan : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := hs.2 ▸ hfE
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hspan

    have hratmem : ∀ i, s i * (s piv)⁻¹ ∈ o.toValuationSubring := fun i => ratio_mem N s hs0 o piv hp i
    have hordpiv : o.ord (s piv) = -(embDivisor N) o :=
      ord_eq_neg_of_forall_le s hs0 hsmem o (bpf_of_span_eq N s hs.2 hdegE o) piv hp
    have hval : ∑ j, a j * evalVec s o j = 0 := by
      have h1 : f * (s piv)⁻¹ = ∑ j, a j • (s j * (s piv)⁻¹) := by
        rw [← ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
      have h2 : o.evalAt (f * (s piv)⁻¹) = ∑ j, a j * evalVec s o j := by
        rw [h1, evalAt_sum_smul_of_mem _ o ho_rat a hratmem]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [evalVec_apply N hr s o j]
      rw [← h2]
      rcases eq_or_ne f 0 with hf0 | hf0
      · rw [hf0, zero_mul, evalAt_zero]
      · have hordf := ((mem_riemannRochSpace_iff.mp hf) o).resolve_left hf0
        rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at hordf
        have hne : f * (s piv)⁻¹ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (hs0 piv))
        have hord : 0 < o.ord (f * (s piv)⁻¹) := by
          rw [o.ord_mul hf0 (inv_ne_zero (hs0 piv)), o.ord_inv, hordpiv]; omega
        exact evalAt_eq_zero_of_ord_pos o ho_rat (o.mem_toValuationSubring_of_ord_nonneg_alt hne hord.le) hord
    have hepiv : evalVec s o piv = 1 := by
      rw [evalVec_apply N hr s o piv, mul_inv_cancel₀ (hs0 piv), Place.evalAt_one]
    have hf_eq : f = ∑ j, a j • chordFun s o (piv, j) := by
      have : ∑ j, a j • chordFun s o (piv, j) = ∑ j, a j • s j - (∑ j, a j * evalVec s o j) • s piv := by
        simp only [chordFun, hepiv, one_smul, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]
      have hz : (∑ j, a j * evalVec s o j) • s piv = 0 := by rw [hval]; exact zero_smul (AlgebraicClosure ℚ) (s piv)
      rw [this, hz, sub_zero, ha]
    rw [hf_eq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(piv, j), rfl⟩)

theorem exists_regVal_chord_ne_zero {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (ht : v₀.ord t = 1) :
    ∃ p : Fin r × Fin r, regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1) ≠ 0 := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]; omega
  have hr : 0 < r := pos_of_span_eq N s hs.2 hdegE
  have hrat := isRational_bar N v₀
  set piv := pivotIndex s v₀ hr with hpiv
  have hp : ∀ j, v₀.ord (s piv) ≤ v₀.ord (s j) := ord_pivot_le N hr s v₀
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := mem_of_span_eq s hs.2
  have hordpiv : v₀.ord (s piv) = -(embDivisor N) v₀ :=
    ord_eq_neg_of_forall_le s hs0 hsmem v₀ (bpf_of_span_eq N s hs.2 hdegE v₀) piv hp
  have ht0 : t ≠ 0 := fun h => by rw [h, Place.ord_zero] at ht; exact zero_ne_one ht

  set D := embDivisor N - Finsupp.single v₀ 1 with hD
  have hdegD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ D.degree := by
    rw [hD, map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N, degree_embDivisor, embDegree_cast]
    push_cast; omega
  obtain ⟨f, hfD, hfnot⟩ := exists_mem_notMem_bar N D hdegD v₀

  have hex : ∃ p : Fin r × Fin r, chordFun s v₀ p ∉ riemannRochSpace (D - Finsupp.single v₀ 1) := by
    by_contra hall
    push Not at hall
    apply hfnot
    have hfspan : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range (chordFun s v₀)) := by
      rw [span_chordFun_eq s hs v₀]; exact hfD
    have hle : Submodule.span (AlgebraicClosure ℚ) (Set.range (chordFun s v₀)) ≤ riemannRochSpace (D - Finsupp.single v₀ 1) :=
      Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact hall p)
    exact hle hfspan
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, ?_⟩
  have hmem : chordFun s v₀ p ∈ riemannRochSpace D := chordFun_mem s hs v₀ p
  have hc0 : chordFun s v₀ p ≠ 0 := fun h => hp (by rw [h]; exact Submodule.zero_mem _)

  have hge : -(embDivisor N v₀) + 1 ≤ v₀.ord (chordFun s v₀ p) := by
    have := ((mem_riemannRochSpace_iff.mp hmem) v₀).resolve_left hc0
    rw [hD, Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at this; omega
  have hord : v₀.ord (chordFun s v₀ p) = -(embDivisor N v₀) + 1 := by
    by_contra hne
    apply hp
    rw [mem_riemannRochSpace_iff]
    intro w
    right
    by_cases hw : w = v₀
    · subst w
      rw [hD, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]
      omega
    · have h1 := ((mem_riemannRochSpace_iff.mp hmem) w).resolve_left hc0
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hw), sub_zero]
      exact h1

  have hg0 : chordFun s v₀ p * ((s piv)⁻¹) ^ 1 * (t⁻¹) ^ 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc0 (pow_ne_zero 1 (inv_ne_zero (hs0 piv)))) (pow_ne_zero 1 (inv_ne_zero ht0))
  have hordg : v₀.ord (chordFun s v₀ p * ((s piv)⁻¹) ^ 1 * (t⁻¹) ^ 1) = 0 := by
    rw [pow_one, pow_one, Place.ord_mul _ (mul_ne_zero hc0 (inv_ne_zero (hs0 piv))) (inv_ne_zero ht0),
      Place.ord_mul _ hc0 (inv_ne_zero (hs0 piv)), Place.ord_inv, Place.ord_inv, hord, hordpiv, ht]
    ring
  have hval : regVal s v₀ t 1 1 (chordFun s v₀ p) = v₀.evalAt (chordFun s v₀ p * ((s piv)⁻¹) ^ 1 * (t⁻¹) ^ 1) := by
    rw [regVal]; simp only [dif_pos hr]; rfl
  show regVal s v₀ t 1 1 (chordFun s v₀ p) ≠ 0
  rw [hval]
  exact v₀.evalAt_ne_zero_of_ord_eq_zero hrat hg0 hordg

end Bar
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero.P2MW"

end P2MYG
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero.P2MW"

open AlgebraicCurve ModularCurve

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (t : modularFunctionFieldBar N) (ht : v₀.ord t = 1) :
    ∃ p : Fin r × Fin r,
      regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1) ≠ 0 := by
  haveI := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  exact P2MYG.exists_regVal_chord_ne_zero s hs v₀ t ht

end S_ModularCurve_JZero_exists_regVal_chord_ne_zero
end P2MW
export P2MW.S_ModularCurve_JZero_exists_regVal_chord_ne_zero (solution)
