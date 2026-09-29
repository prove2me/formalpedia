-- Prove2me | solution 1 for ModularCurve.JZero.exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/37e3c22d-edfb-5e31-bf7a-5a0e211b5400

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_constantsAreBase_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_add_pointHt_le
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply"

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

section Der

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]

theorem exists_eq_smul_D {t : F} (hDt : D K F t ≠ 0) (ω : Ω[F⁄K]) : ∃ g : F, ω = g • D K F t := by
  have h1 := (finrank_eq_one_iff_of_nonzero' (D K F t) hDt).mp IsCurveOver.finrank_kaehler ω
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc.symm⟩

theorem diffCoeff_smul_D' {t : F} (hDt : D K F t ≠ 0) (ω : Ω[F⁄K]) :
    Place.diffCoeff t ω • D K F t = ω :=
  Place.diffCoeff_smul_D (exists_eq_smul_D hDt ω)

theorem diffCoeff_eq_of_smul_D_eq {t : F} (hDt : D K F t ≠ 0) {g : F} {ω : Ω[F⁄K]} (h : g • D K F t = ω) :
    Place.diffCoeff t ω = g := by
  have key : (Place.diffCoeff t ω - g) • D K F t = 0 := by
    rw [sub_smul, diffCoeff_smul_D' hDt ω, h, sub_self]
  rcases smul_eq_zero.mp key with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hDt

theorem diffCoeff_add' {t : F} (hDt : D K F t ≠ 0) (ω₁ ω₂ : Ω[F⁄K]) :
    Place.diffCoeff t (ω₁ + ω₂) = Place.diffCoeff t ω₁ + Place.diffCoeff t ω₂ :=
  diffCoeff_eq_of_smul_D_eq hDt (by rw [add_smul, diffCoeff_smul_D' hDt, diffCoeff_smul_D' hDt])

theorem diffCoeff_smul' {t : F} (hDt : D K F t ≠ 0) (c : F) (ω : Ω[F⁄K]) :
    Place.diffCoeff t (c • ω) = c * Place.diffCoeff t ω :=
  diffCoeff_eq_of_smul_D_eq hDt (by rw [mul_smul, diffCoeff_smul_D' hDt])

theorem diffCoeff_sub' {t : F} (hDt : D K F t ≠ 0) (ω₁ ω₂ : Ω[F⁄K]) :
    Place.diffCoeff t (ω₁ - ω₂) = Place.diffCoeff t ω₁ - Place.diffCoeff t ω₂ := by
  rw [sub_eq_add_neg, diffCoeff_add' hDt, ← neg_one_smul F ω₂, diffCoeff_smul' hDt]; ring

theorem diffCoeff_zero' {t : F} (hDt : D K F t ≠ 0) : Place.diffCoeff t (0 : Ω[F⁄K]) = 0 :=
  diffCoeff_eq_of_smul_D_eq hDt (zero_smul F _)

theorem diffCoeff_D_self {t : F} (hDt : D K F t ≠ 0) : Place.diffCoeff t (D K F t) = 1 :=
  diffCoeff_eq_of_smul_D_eq hDt (one_smul F _)

variable (K) in

def der (t f : F) : F := Place.diffCoeff t (D K F f)

theorem der_smul_D {t : F} (hDt : D K F t ≠ 0) (f : F) : der K t f • D K F t = D K F f :=
  diffCoeff_smul_D' hDt _

theorem der_add {t : F} (hDt : D K F t ≠ 0) (f g : F) : der K t (f + g) = der K t f + der K t g := by
  unfold der; rw [map_add, diffCoeff_add' hDt]

theorem der_sub {t : F} (hDt : D K F t ≠ 0) (f g : F) : der K t (f - g) = der K t f - der K t g := by
  unfold der; rw [map_sub, diffCoeff_sub' hDt]

theorem der_mul {t : F} (hDt : D K F t ≠ 0) (f g : F) :
    der K t (f * g) = f * der K t g + g * der K t f := by
  unfold der; rw [Derivation.leibniz, diffCoeff_add' hDt, diffCoeff_smul' hDt, diffCoeff_smul' hDt]

theorem der_algebraMap {t : F} (hDt : D K F t ≠ 0) (c : K) : der K t (algebraMap K F c) = 0 := by
  unfold der; rw [Derivation.map_algebraMap, diffCoeff_zero' hDt]

theorem der_one {t : F} (hDt : D K F t ≠ 0) : der K t (1 : F) = 0 := by
  rw [← map_one (algebraMap K F), der_algebraMap hDt]

theorem der_self {t : F} (hDt : D K F t ≠ 0) : der K t t = 1 := diffCoeff_D_self hDt

theorem der_zero {t : F} (hDt : D K F t ≠ 0) : der K t (0 : F) = 0 := by
  unfold der; rw [map_zero, diffCoeff_zero' hDt]

theorem der_smul {t : F} (hDt : D K F t ≠ 0) (c : K) (f : F) : der K t (c • f) = c • der K t f := by
  rw [Algebra.smul_def, der_mul hDt, der_algebraMap hDt, mul_zero, add_zero, Algebra.smul_def]

theorem der_sum_smul {t : F} (hDt : D K F t ≠ 0) {ι : Type*} (S : Finset ι) (c : ι → K) (f : ι → F) :
    der K t (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i • der K t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact der_zero hDt
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, der_add hDt, der_smul hDt, ih]

theorem der_pow_two {t : F} (hDt : D K F t ≠ 0) (f : F) : der K t (f ^ 2) = 2 * f * der K t f := by
  rw [pow_two, der_mul hDt]; ring

theorem der_chain {t t' : F} (hDt : D K F t ≠ 0) (hDt' : D K F t' ≠ 0) (f : F) :
    der K t f = der K t' f * der K t t' :=
  diffCoeff_eq_of_smul_D_eq hDt (by rw [mul_smul, der_smul_D hDt, der_smul_D hDt'])

theorem der_ne_zero_of_chain {t t' : F} (hDt : D K F t ≠ 0) (hDt' : D K F t' ≠ 0) : der K t t' ≠ 0 := by
  intro h
  have := der_smul_D hDt t'
  rw [h, zero_smul] at this
  exact hDt' this.symm

variable (K) in

def wr (t f g : F) : F := f * der K t g - g * der K t f

theorem wr_eq_diffCoeff {t : F} (hDt : D K F t ≠ 0) (f g : F) :
    wr K t f g = Place.diffCoeff t (f • D K F g - g • D K F f) := by
  rw [diffCoeff_sub' hDt, diffCoeff_smul' hDt, diffCoeff_smul' hDt]; rfl

theorem wr_mul_mul {t : F} (hDt : D K F t ≠ 0) (p f g : F) :
    wr K t (p * f) (p * g) = p ^ 2 * wr K t f g := by
  unfold wr; rw [der_mul hDt, der_mul hDt]; ring

theorem wr_chain {t t' : F} (hDt : D K F t ≠ 0) (hDt' : D K F t' ≠ 0) (f g : F) :
    wr K t f g = wr K t' f g * der K t t' := by
  unfold wr; rw [der_chain hDt hDt' f, der_chain hDt hDt' g]; ring

theorem wr_one_left {t : F} (hDt : D K F t ≠ 0) (g : F) : wr K t 1 g = der K t g := by
  unfold wr; rw [der_one hDt]; ring

omit [IsCurveOver K F] in
theorem wr_self (t f : F) : wr K t f f = 0 := by unfold wr; ring

theorem der_smul_sub_smul {t : F} (hDt : D K F t ≠ 0) (a b : K) (f g : F) :
    der K t (a • g - b • f) = a • der K t g - b • der K t f := by
  rw [der_sub hDt, der_smul hDt, der_smul hDt]

end Der

section Local

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] [IsCurveOver K F]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]

include x in

theorem D_ne_zero_of_ord_eq_one (w : Place K F) {t : F} (ht : w.ord t = 1) : D K F t ≠ 0 := by
  haveI : PerfectField K := PerfectField.ofCharZero
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have := Place.diffCoeff_smul_D_of_ord_eq_one x w ht ω
  rw [h0, smul_zero] at this
  exact hω this.symm

include x in

theorem der_mem (w : Place K F) {t : F} (ht : w.ord t = 1) {f : F} (hf : f ∈ w.toValuationSubring) :
    der K t f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · unfold der; rw [map_zero, diffCoeff_zero' (D_ne_zero_of_ord_eq_one x w ht)]; exact zero_mem _
  · apply mem_of_eq_zero_or_ord_nonneg
    rcases eq_or_ne (der K t f) 0 with h | h
    · exact Or.inl h
    · exact Or.inr (Place.ord_diffCoeff_D_nonneg x w ht (ord_nonneg_of_mem w hf0 hf))

include x in
theorem wr_mem (w : Place K F) {t : F} (ht : w.ord t = 1) {f g : F} (hf : f ∈ w.toValuationSubring)
    (hg : g ∈ w.toValuationSubring) : wr K t f g ∈ w.toValuationSubring :=
  sub_mem (mul_mem hf (der_mem x w ht hg)) (mul_mem hg (der_mem x w ht hf))

include x in
omit [IsCurveOver K F] in

theorem ord_diffCoeff_eq_ordDiff (w : Place K F) {t : F} (ht : w.ord t = 1) (ω : Ω[F⁄K]) :
    w.ord (Place.diffCoeff t ω) = w.ordDiff ω :=
  (Place.ordDiff_eq_ord_diffCoeff x w ht ω).symm

include x in

theorem evalAt_mul_inv_eq_evalAt_der (w : Place K F) (hw : w.IsRational) {t f : F} (ht : w.ord t = 1)
    (hf0 : f ≠ 0) (hf : 1 ≤ w.ord f) :
    w.evalAt (f * t⁻¹) = w.evalAt (der K t f) := by
  have hDt := D_ne_zero_of_ord_eq_one x w ht
  have ht0 : t ≠ 0 := fun h => by rw [h, w.ord_zero] at ht; exact zero_ne_one ht
  set g : F := f * t⁻¹ with hg
  have hg0 : g ≠ 0 := mul_ne_zero hf0 (inv_ne_zero ht0)
  have hordg : 0 ≤ w.ord g := by rw [hg, w.ord_mul hf0 (inv_ne_zero ht0), w.ord_inv, ht]; omega
  have hgmem : g ∈ w.toValuationSubring := w.mem_toValuationSubring_of_ord_nonneg_alt hg0 hordg
  have htmem : t ∈ w.toValuationSubring := w.mem_toValuationSubring_of_ord_nonneg_alt ht0 (by rw [ht]; norm_num)
  have hfg : f = t * g := by rw [hg]; field_simp
  have hDf : der K t f = t * der K t g + g := by
    rw [hfg, der_mul hDt, der_self hDt]; ring
  have hcmem : der K t g ∈ w.toValuationSubring := der_mem x w ht hgmem
  rw [hDf, evalAt_add_of_mem w hw (mul_mem htmem hcmem) hgmem, w.evalAt_mul_of_mem hw htmem hcmem,
    evalAt_eq_zero_of_ord_pos w hw htmem (by rw [ht]; norm_num), zero_mul, zero_add]

include x in

theorem evalAt_der_ne_zero_of_ord_eq_one (w : Place K F) (hw : w.IsRational) {t f : F} (ht : w.ord t = 1)
    (hf : w.ord f = 1) : w.evalAt (der K t f) ≠ 0 := by
  have hf0 : f ≠ 0 := fun h => by rw [h, w.ord_zero] at hf; exact zero_ne_one hf
  have ht0 : t ≠ 0 := fun h => by rw [h, w.ord_zero] at ht; exact zero_ne_one ht
  rw [← evalAt_mul_inv_eq_evalAt_der x w hw ht hf0 hf.ge]
  refine w.evalAt_ne_zero_of_ord_eq_zero hw (mul_ne_zero hf0 (inv_ne_zero ht0)) ?_
  rw [w.ord_mul hf0 (inv_ne_zero ht0), w.ord_inv, ht, hf]; norm_num

end Local

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

section WrLocal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  [HasCanonicalDivisor (K := K) (F := F)]
  (x' : F) [FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F)) F]

include x' in

theorem ord_der_eq_canonical (w : Place K F) {t : F} (ht : w.ord t = 1) {x : F} (hx : D K F x ≠ 0) :
    w.ord (der K t x) = canonicalDivisorOf hx w := by
  unfold der
  rw [ord_diffCoeff_eq_ordDiff x' w ht, Place.ordDiff_eq_ordDifferential, canonicalDivisorOf_apply]

include x' in

theorem diffCoeff_mul_der_eq (w : Place K F) {t : F} (ht : w.ord t = 1) {x : F} (hx : D K F x ≠ 0)
    (si sj sp : F) (hsp : sp ≠ 0) :
    Place.diffCoeff x (si • D K F sj - sj • D K F si) * der K t x
      = sp ^ 2 * wr K t (si * sp⁻¹) (sj * sp⁻¹) := by
  have hDt := D_ne_zero_of_ord_eq_one x' w ht
  rw [← wr_eq_diffCoeff hx, ← wr_chain hDt hx, ← wr_mul_mul hDt]
  congr 1 <;> field_simp

include x' in

theorem diffCoeff_wr_zero_or_le (w : Place K F) {t : F} (ht : w.ord t = 1) {x : F} (hx : D K F x ≠ 0)
    {si sj sp : F} (hsp : sp ≠ 0) {d : ℤ} (hord : -d ≤ w.ord sp)
    (hi : si * sp⁻¹ ∈ w.toValuationSubring) (hj : sj * sp⁻¹ ∈ w.toValuationSubring) :
    Place.diffCoeff x (si • D K F sj - sj • D K F si) = 0 ∨
      -(2 * d + canonicalDivisorOf hx w) ≤ w.ord (Place.diffCoeff x (si • D K F sj - sj • D K F si)) := by
  set W := Place.diffCoeff x (si • D K F sj - sj • D K F si) with hW
  rcases eq_or_ne W 0 with h0 | h0
  · exact Or.inl h0
  · right
    have hDt := D_ne_zero_of_ord_eq_one x' w ht
    have hdx0 : der K t x ≠ 0 := der_ne_zero_of_chain hDt hx
    have key := diffCoeff_mul_der_eq x' w ht hx si sj sp hsp
    rw [← hW] at key
    have hwr0 : wr K t (si * sp⁻¹) (sj * sp⁻¹) ≠ 0 := by
      intro h; rw [h, mul_zero] at key; exact (mul_ne_zero h0 hdx0) key
    have hwrmem := wr_mem x' w ht hi hj
    have h1 : w.ord W + w.ord (der K t x) = 2 * w.ord sp + w.ord (wr K t (si * sp⁻¹) (sj * sp⁻¹)) := by
      rw [← w.ord_mul h0 hdx0, key, w.ord_mul (pow_ne_zero 2 hsp) hwr0, pow_two, w.ord_mul hsp hsp]; ring
    rw [ord_der_eq_canonical x' w ht hx] at h1
    have h2 := ord_nonneg_of_mem w hwr0 hwrmem
    linarith

end WrLocal

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

namespace P2MW

open AlgebraicCurve ModularCurve KaehlerDifferential

section BarW

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

omit [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
theorem ratio_mem {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j))
    (i : Fin r) : s i * (s p)⁻¹ ∈ w.toValuationSubring :=
  w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 p)))
    (by rw [w.ord_mul (hs0 i) (inv_ne_zero (hs0 p)), w.ord_inv]; linarith [hp i])

omit [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
theorem nsmul_two_add_apply (D K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : (2 • D + K₀) w = 2 * D w + K₀ w := by
  rw [two_nsmul, Finsupp.add_apply, Finsupp.add_apply]; ring

end BarW
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

namespace P2MW

open AlgebraicCurve

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

theorem absLogHeight_smul {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : absLogHeight (c • x) = absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (insert c (Set.range x)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert c _)
  have hx' : ∀ i, x i ∈ E' := fun i =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem c ⟨i, rfl⟩)
  have hcx : ∀ i, (c • x) i ∈ E' := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]; exact mul_mem hcE (hx' i)
  rw [absLogHeight_eq_of_mem (c • x) E' hcx, absLogHeight_eq_of_mem x E' hx']
  congr 1
  convert Height.logHeight_smul_eq_logHeight (fun i => (⟨x i, hx' i⟩ : E')) (c := ⟨c, hcE⟩) ?_ using 2
  all_goals first
    | exact fun h0 => hc (by simpa using congrArg Subtype.val h0)
    | (funext i; apply Subtype.ext; simp [Pi.smul_apply, smul_eq_mul])

theorem absLogHeight_linear_le {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι]
    (M : κ → ι → AlgebraicClosure ℚ) (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (fun j => ∑ i, M j i * x i)
      ≤ Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2) + absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range (fun q : κ × ι => M q.1 q.2)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hME : ∀ q : κ × ι, M q.1 q.2 ∈ E' := fun q => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨q, rfl⟩)
  have hyE : ∀ j, (∑ i, M j i * x i) ∈ E' := fun j => sum_mem fun i _ => mul_mem (hME (j, i)) (hxE i)
  rw [absLogHeight_eq_of_mem _ E' hyE, absLogHeight_eq_of_mem _ E' hME, absLogHeight_eq_of_mem x E' hxE]
  have hd : (0 : ℝ) < Module.finrank ℚ E' := by exact_mod_cast Module.finrank_pos
  have hfun : (fun j => (⟨∑ i, M j i * x i, hyE j⟩ : E'))
      = fun j => ∑ i, (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E') := by
    funext j
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
  have key := Height.logHeight_linearMap_apply_le (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
    (fun i => (⟨x i, hxE i⟩ : E'))
  rw [NumberField.totalWeight_eq_finrank, Nat.card_eq_fintype_card] at key
  rw [hfun]
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  calc (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun j => ∑ i,
          (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E'))
      ≤ (Module.finrank ℚ E' : ℝ)⁻¹ * ((Module.finrank ℚ E' : ℝ) * Real.log (Fintype.card ι)
          + Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + Height.logHeight (fun i => (⟨x i, hxE i⟩ : E'))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hd.le)
    _ = Real.log (Fintype.card ι)
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hxE i⟩ : E')) := by
        field_simp

theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem absLogHeight_reindex_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι] [Nonempty κ]
    (e : κ → ι) (he : Function.Injective e) :
    ∃ C : ℝ, ∀ y : ι → AlgebraicClosure ℚ, (∀ p, p ∉ Set.range e → y p = 0) →
      |absLogHeight (y ∘ e) - absLogHeight y| ≤ C := by
  classical
  let M : κ → ι → AlgebraicClosure ℚ := fun k p => if p = e k then 1 else 0
  let M' : ι → κ → AlgebraicClosure ℚ := fun p k => if p = e k then 1 else 0
  refine ⟨Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2)
    + (Real.log (Fintype.card κ) + absLogHeight (fun q : ι × κ => M' q.1 q.2)), fun y hy => ?_⟩
  have h1 : (y ∘ e) = fun k => ∑ p, M k p * y p := by
    funext k
    simp only [Function.comp_apply, M, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (e k) (fun p => y p)]
    simp
  have h2 : y = fun p => ∑ k, M' p k * (y ∘ e) k := by
    funext p
    simp only [Function.comp_apply, M', ite_mul, one_mul, zero_mul]
    by_cases hp : p ∈ Set.range e
    · obtain ⟨k₀, rfl⟩ := hp
      rw [Finset.sum_eq_single k₀]
      · simp
      · intro k _ hk
        rw [if_neg]
        intro h; exact hk (he h.symm)
      · intro h; exact absurd (Finset.mem_univ k₀) h
    · rw [hy p hp]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro h; exact hp ⟨k, h.symm⟩
  have hA := absLogHeight_linear_le M y
  have hB := absLogHeight_linear_le M' (y ∘ e)
  rw [← h1] at hA
  rw [← h2] at hB
  have hlι : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hlκ : 0 ≤ Real.log (Fintype.card κ : ℝ) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hM := absLogHeight_nonneg (fun q : κ × ι => M q.1 q.2)
  have hM' := absLogHeight_nonneg (fun q : ι × κ => M' q.1 q.2)
  rw [abs_le]
  constructor <;> linarith

end AbsHeight
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

namespace P2MW

open AlgebraicCurve ModularCurve KaehlerDifferential

section WqDef

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K) in

noncomputable def wq {r : ℕ} (x : F) (s : Fin r → F) (q : Fin r × Fin r) : F :=
  Place.diffCoeff x (s q.1 • KaehlerDifferential.D K F (s q.2) - s q.2 • KaehlerDifferential.D K F (s q.1))

theorem wq_apply {r : ℕ} (x : F) (s : Fin r → F) (i j : Fin r) :
    wq K x s (i, j) = Place.diffCoeff x (s i • KaehlerDifferential.D K F (s j) - s j • KaehlerDifferential.D K F (s i)) :=
  rfl

theorem canonicalDivisorOf_smul_D_apply [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] {x a : F} (hx : KaehlerDifferential.D K F x ≠ 0) (ha0 : a ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ha : a • KaehlerDifferential.D K F x = ω₀) (w : Place K F) :
    canonicalDivisorOf hω₀ w = w.ord a + canonicalDivisorOf hx w := by
  haveI : w.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver w
  have hc : w.differentialCoeff (KaehlerDifferential.D K F x) ≠ 0 := by
    intro h0
    have := w.differentialCoeff_smul_dCoord (KaehlerDifferential.D K F x)
    rw [h0, zero_smul] at this
    exact hx this.symm
  rw [canonicalDivisorOf_apply, canonicalDivisorOf_apply, ← ha]
  exact w.ordDifferential_smul ha0 hc

end WqDef
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

section BarT

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

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

theorem regVal_chord_eq_evalAt_wr (x' : modularFunctionFieldBar N)
    [FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {t : modularFunctionFieldBar N} (ht : v.ord t = 1)
    (i j : Fin r) :
    regVal s v t 1 1 (evalVec s v i • s j - evalVec s v j • s i)
      = v.evalAt (wr (AlgebraicClosure ℚ) t (s i * (s (pivotIndex s v hr))⁻¹) (s j * (s (pivotIndex s v hr))⁻¹)) := by
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  have hv := isRational_bar N v
  have hDt := D_ne_zero_of_ord_eq_one x' v ht
  set p := pivotIndex s v hr with hp_def
  have hp : ∀ j, v.ord (s p) ≤ v.ord (s j) := ord_pivot_le N hr s v
  set fi := s i * (s p)⁻¹ with hfi_def
  set fj := s j * (s p)⁻¹ with hfj_def
  have hfi : fi ∈ v.toValuationSubring := ratio_mem N s hs0 v p hp i
  have hfj : fj ∈ v.toValuationSubring := ratio_mem N s hs0 v p hp j
  have hdfi := der_mem x' v ht hfi
  have hdfj := der_mem x' v ht hfj
  have hei : evalVec s v i = v.evalAt fi := evalVec_apply N hr s v i
  have hej : evalVec s v j = v.evalAt fj := evalVec_apply N hr s v j
  rw [regVal_apply N hr]
  set g := evalVec s v i • fj - evalVec s v j • fi with hg
  have harg : (evalVec s v i • s j - evalVec s v j • s i) * (s p)⁻¹ ^ 1 * t⁻¹ ^ 1 = g * t⁻¹ := by
    rw [pow_one, pow_one, hg, sub_mul, smul_mul_assoc, smul_mul_assoc]
  rw [harg]
  have hgmem : g ∈ v.toValuationSubring := sub_mem (smul_mem_of_mem v _ hfj) (smul_mem_of_mem v _ hfi)
  have hgval : v.evalAt g = 0 := by
    rw [hg, evalAt_sub_of_mem v hv (smul_mem_of_mem v _ hfj) (smul_mem_of_mem v _ hfi),
      evalAt_smul_of_mem v hv _ hfj, evalAt_smul_of_mem v hv _ hfi, hei, hej]; ring
  have hwr_val : v.evalAt (wr (AlgebraicClosure ℚ) t fi fj)
      = evalVec s v i * v.evalAt (der (AlgebraicClosure ℚ) t fj) - evalVec s v j * v.evalAt (der (AlgebraicClosure ℚ) t fi) := by
    unfold wr
    rw [evalAt_sub_of_mem v hv (mul_mem hfi hdfj) (mul_mem hfj hdfi), v.evalAt_mul_of_mem hv hfi hdfj,
      v.evalAt_mul_of_mem hv hfj hdfi, hei, hej]
  have hderg : der (AlgebraicClosure ℚ) t g
      = evalVec s v i • der (AlgebraicClosure ℚ) t fj - evalVec s v j • der (AlgebraicClosure ℚ) t fi := by
    rw [hg]; exact der_smul_sub_smul hDt _ _ fi fj
  have hderg_val : v.evalAt (der (AlgebraicClosure ℚ) t g)
      = evalVec s v i * v.evalAt (der (AlgebraicClosure ℚ) t fj) - evalVec s v j * v.evalAt (der (AlgebraicClosure ℚ) t fi) := by
    rw [hderg, evalAt_sub_of_mem v hv (smul_mem_of_mem v _ hdfj) (smul_mem_of_mem v _ hdfi),
      evalAt_smul_of_mem v hv _ hdfj, evalAt_smul_of_mem v hv _ hdfi]
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [hg0, zero_mul, evalAt_zero, hwr_val, ← hderg_val, hg0, der_zero hDt, evalAt_zero]
  · have hord : 1 ≤ v.ord g := by
      have := ord_pos_of_evalAt_eq_zero v hv hg0 hgmem hgval; omega
    rw [evalAt_mul_inv_eq_evalAt_der x' v hv ht hg0 hord, hderg_val, hwr_val]

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

theorem exists_wronskian_family {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    {x a : modularFunctionFieldBar N} (ha0 : a ≠ 0)
    (Kx K₀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hK : ∀ w, K₀ w = w.ord a + Kx w)
    (hWmem : ∀ i j, Place.diffCoeff x (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
        - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s i))
        ∈ riemannRochSpace (2 • D + Kx))
    (hWbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i j,
      Place.diffCoeff x (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
        - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s i)) ≠ 0 ∧
      w.ord (Place.diffCoeff x (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
        - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s i))) + (2 • D + Kx) w = 0) :
    ∃ (b : ℕ) (e : Fin b → Fin r × Fin r) (u : Fin b → modularFunctionFieldBar N),
      Function.Injective e ∧
      (∀ k, u k = wq (AlgebraicClosure ℚ) x s (e k) * a⁻¹) ∧
      (∀ q, wq (AlgebraicClosure ℚ) x s q ≠ 0 → q ∈ Set.range e) ∧
      (∀ k, u k ≠ 0) ∧
      (∀ k, u k ∈ riemannRochSpace (D + (D + K₀))) ∧
      (∀ w, ∃ k, w.ord (u k) + (D + (D + K₀)) w = 0) := by
  classical
  let S : Finset (Fin r × Fin r) := Finset.univ.filter (fun q => wq (AlgebraicClosure ℚ) x s q ≠ 0)
  let e : Fin S.card → Fin r × Fin r := fun k => ((S.equivFin.symm k : S) : Fin r × Fin r)
  have he_mem : ∀ k, e k ∈ S := fun k => (S.equivFin.symm k).2
  have he_inj : Function.Injective e := fun k k' h =>
    S.equivFin.symm.injective (Subtype.ext h)
  have hWx_e : ∀ k, wq (AlgebraicClosure ℚ) x s (e k) ≠ 0 := fun k => (Finset.mem_filter.mp (he_mem k)).2
  have hS_of : ∀ q, wq (AlgebraicClosure ℚ) x s q ≠ 0 → q ∈ Set.range e := fun q hq =>
    ⟨S.equivFin ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩, by simp [e]⟩
  have hD₂w : ∀ w, (D + (D + K₀)) w = 2 * D w + K₀ w := by
    intro w; rw [Finsupp.add_apply, Finsupp.add_apply]; ring
  refine ⟨S.card, e, fun k => wq (AlgebraicClosure ℚ) x s (e k) * a⁻¹, he_inj, fun k => rfl, hS_of,
    fun k => mul_ne_zero (hWx_e k) (inv_ne_zero ha0), fun k => ?_, fun w => ?_⟩
  · rw [mem_riemannRochSpace_iff]
    intro w
    right
    have h1 := ((mem_riemannRochSpace_iff.mp (hWmem (e k).1 (e k).2)) w).resolve_left (hWx_e k)
    rw [nsmul_two_add_apply] at h1
    rw [w.ord_mul (hWx_e k) (inv_ne_zero ha0), w.ord_inv, hD₂w, hK w]
    change -((2 : ℤ) * D w + Kx w) ≤ w.ord (wq (AlgebraicClosure ℚ) x s (e k)) at h1
    linarith
  · obtain ⟨i, j, hne, hord⟩ := hWbpf w
    obtain ⟨k, hk⟩ := hS_of (i, j) hne
    refine ⟨k, ?_⟩
    rw [nsmul_two_add_apply] at hord
    rw [w.ord_mul (hWx_e k) (inv_ne_zero ha0), w.ord_inv, hD₂w, hK w, hk, wq_apply]
    linarith

theorem evalVec_wronskian_family (x : modularFunctionFieldBar N)
    [FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    (hx : KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) x ≠ 0)
    {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ Divisor.degree D)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    {a : modularFunctionFieldBar N} (ha0 : a ≠ 0) (K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hK : ∀ w, K₀ w = w.ord a + canonicalDivisorOf hx w)
    {b : ℕ} (hb : 0 < b) (e : Fin b → Fin r × Fin r) (u : Fin b → modularFunctionFieldBar N)
    (hu : ∀ k, u k = wq (AlgebraicClosure ℚ) x s (e k) * a⁻¹)
    (hS : ∀ q, wq (AlgebraicClosure ℚ) x s q ≠ 0 → q ∈ Set.range e)
    (hu0 : ∀ k, u k ≠ 0)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hbpfv : ∃ k, v.ord (u k) + (D + (D + K₀)) v = 0)
    {t : modularFunctionFieldBar N} (ht : v.ord t = 1) :
    (∀ q, q ∉ Set.range e →
        regVal s v t 1 1 (evalVec s v q.1 • s q.2 - evalVec s v q.2 • s q.1) = 0) ∧
    ∃ μ : AlgebraicClosure ℚ, μ ≠ 0 ∧
      evalVec u v = μ • ((fun q : Fin r × Fin r =>
        regVal s v t 1 1 (evalVec s v q.1 • s q.2 - evalVec s v q.2 • s q.1)) ∘ e) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hEFT : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  have hv := isRational_bar N v
  have hDt := D_ne_zero_of_ord_eq_one x v ht
  have hdx0 : der (AlgebraicClosure ℚ) t x ≠ 0 := der_ne_zero_of_chain hDt hx
  have hsmem : ∀ i, s i ∈ riemannRochSpace D := mem_of_span_eq s hsD
  set p := pivotIndex s v hr with hp_def
  have hp : ∀ j, v.ord (s p) ≤ v.ord (s j) := ord_pivot_le N hr s v

  set wrq : Fin r × Fin r → modularFunctionFieldBar N :=
    fun q => wr (AlgebraicClosure ℚ) t (s q.1 * (s p)⁻¹) (s q.2 * (s p)⁻¹) with hwrq_def
  have hwrmem : ∀ q, wrq q ∈ v.toValuationSubring := fun q =>
    wr_mem x v ht (ratio_mem N s hs0 v p hp q.1) (ratio_mem N s hs0 v p hp q.2)
  set y : Fin r × Fin r → AlgebraicClosure ℚ := fun q =>
    regVal s v t 1 1 (evalVec s v q.1 • s q.2 - evalVec s v q.2 • s q.1) with hy_def
  have hy : ∀ q, y q = v.evalAt (wrq q) := fun q =>
    regVal_chord_eq_evalAt_wr N x hr s hs0 v ht q.1 q.2

  have hloc : ∀ q, wq (AlgebraicClosure ℚ) x s q * der (AlgebraicClosure ℚ) t x = (s p) ^ 2 * wrq q := fun q =>
    diffCoeff_mul_der_eq x v ht hx (s q.1) (s q.2) (s p) (hs0 p)
  refine ⟨fun q hq => ?_, ?_⟩
  ·
    have hWq : wq (AlgebraicClosure ℚ) x s q = 0 := by
      by_contra hne
      exact hq (hS q hne)
    have hwr0 : wrq q = 0 := by
      have := hloc q
      rw [hWq, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero 2 (hs0 p))
    show y q = 0
    rw [hy q, hwr0, evalAt_zero]
  ·
    have hordp : v.ord (s p) = -D v :=
      ord_eq_neg_of_forall_le s hs0 hsmem v (bpf_of_span_eq N s hsD (by omega) v) p hp
    have horda : v.ord (a * der (AlgebraicClosure ℚ) t x) = K₀ v := by
      rw [v.ord_mul ha0 hdx0, ord_der_eq_canonical x v ht hx, hK v]
    have hadx0 : a * der (AlgebraicClosure ℚ) t x ≠ 0 := mul_ne_zero ha0 hdx0
    have hu_loc : ∀ k, u k = (s p) ^ 2 * wrq (e k) * (a * der (AlgebraicClosure ℚ) t x)⁻¹ := by
      intro k
      rw [hu k, ← hloc (e k)]
      field_simp
    have hwr_e0 : ∀ k, wrq (e k) ≠ 0 := by
      intro k h0
      apply hu0 k
      rw [hu_loc k, h0, mul_zero, zero_mul]
    have hord_u : ∀ k, v.ord (u k) = -(2 * D v + K₀ v) + v.ord (wrq (e k)) := by
      intro k
      rw [hu_loc k, v.ord_mul (mul_ne_zero (pow_ne_zero 2 (hs0 p)) (hwr_e0 k)) (inv_ne_zero hadx0),
        v.ord_mul (pow_ne_zero 2 (hs0 p)) (hwr_e0 k), v.ord_inv, horda, pow_two, v.ord_mul (hs0 p) (hs0 p), hordp]
      ring

    set qu := pivotIndex u v hb with hqu_def
    have hqu : ∀ k, v.ord (u qu) ≤ v.ord (u k) := ord_pivot_le N hb u v
    have hunit : v.ord (wrq (e qu)) = 0 := by
      obtain ⟨k₀, hk₀⟩ := hbpfv
      rw [Finsupp.add_apply, Finsupp.add_apply] at hk₀
      have h1 : v.ord (wrq (e k₀)) = 0 := by rw [hord_u k₀] at hk₀; linarith
      have h2 := hqu k₀
      rw [hord_u, hord_u, h1] at h2
      have h3 := ord_nonneg_of_mem v (hwr_e0 qu) (hwrmem (e qu))
      linarith
    have hlam : v.evalAt (wrq (e qu)) ≠ 0 := v.evalAt_ne_zero_of_ord_eq_zero hv (hwr_e0 qu) hunit
    set μ : AlgebraicClosure ℚ := v.evalAt (wrq (e qu))⁻¹ with hμ_def
    have hμ : v.evalAt (wrq (e qu)) * μ = 1 := evalAt_mul_evalAt_inv v hv (hwr_e0 qu) hunit
    have hμ0 : μ ≠ 0 := fun h => by rw [h, mul_zero] at hμ; exact zero_ne_one hμ
    refine ⟨μ, hμ0, ?_⟩
    funext k
    rw [evalVec_apply N hb u v k, ← hqu_def, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    show v.evalAt (u k * (u qu)⁻¹) = μ * y (e k)
    rw [hy]
    have hratio : u k * (u qu)⁻¹ = wrq (e k) * (wrq (e qu))⁻¹ := by
      rw [hu_loc k, hu_loc qu]
      field_simp [hs0 p]
    rw [hratio, v.evalAt_mul_of_mem hv (hwrmem (e k)) (inv_mem_of_ord_eq_zero v (hwr_e0 qu) hunit), hμ_def]
    ring

theorem tangent_main {r c : ℕ} (s : Fin r → modularFunctionFieldBar N) (w : Fin c → modularFunctionFieldBar N)
    (hs0 : ∀ i, s i ≠ 0) (hw0 : ∀ l, w l ≠ 0)
    (hg : 1 ≤ genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ Divisor.degree D)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    {ω₀ : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω₀ : ω₀ ≠ 0)
    (hwD : Submodule.span (AlgebraicClosure ℚ) (Set.range w) = riemannRochSpace (D + canonicalDivisorOf hω₀)) :
    ∃ C : ℝ, ∀ (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
      v.ord t = 1 →
      |absLogHeight (fun p : Fin r × Fin r =>
          regVal s v t 1 1 (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
        - (pointHt s v + pointHt w v)| ≤ C := by
  classical

  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hEFT : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  obtain ⟨x, hxT, hxfd, hxsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)
  haveI := hxfd
  haveI := hxsep
  have hx : KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental (AlgebraicClosure ℚ) x hxT
  have hr : 0 < r := pos_of_span_eq N s hsD (by omega)
  haveI : Nonempty (Fin r × Fin r) := ⟨(⟨0, hr⟩, ⟨0, hr⟩)⟩

  obtain ⟨hWmem, hWbpf⟩ :=
    ModularCurve.JZero.diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero N s hs0 D hD hsD hx
  have ha : Place.diffCoeff x ω₀ • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) x = ω₀ :=
    diffCoeff_smul_D' hx ω₀
  have ha0 : Place.diffCoeff x ω₀ ≠ 0 := fun h => hω₀ (by rw [← ha, h, zero_smul])
  have hK : ∀ w', canonicalDivisorOf hω₀ w' = w'.ord (Place.diffCoeff x ω₀) + canonicalDivisorOf hx w' :=
    canonicalDivisorOf_smul_D_apply hx ha0 hω₀ ha

  obtain ⟨b, e, u, he, hu, hS, hu0, huD, hbpf⟩ :=
    exists_wronskian_family N s ha0 (canonicalDivisorOf hx) (canonicalDivisorOf hω₀) D hK hWmem hWbpf
  have hb : 0 < b := by
    obtain ⟨k, -⟩ := hbpf (cuspInftyBar N)
    exact Fin.pos k
  haveI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩

  have hdegK : (canonicalDivisorOf hω₀).degree = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 2 := by
    rw [degree_canonicalDivisorOf_modularFunctionFieldBar N hω₀, genus_eq_genusFF_modularFunctionFieldBar N]
  have hg1 : (1 : ℤ) ≤ (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by exact_mod_cast hg
  have hDK : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1
      ≤ (D + canonicalDivisorOf hω₀).degree := by
    rw [map_add, hdegK]; linarith
  have hD₂ : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1
      ≤ (D + (D + canonicalDivisorOf hω₀)).degree := by
    rw [map_add, map_add, hdegK]; linarith
  obtain ⟨c₂, s₂, hs₂0, hs₂D⟩ := exists_family_span_eq N (D + (D + canonicalDivisorOf hω₀))
  obtain ⟨C₁, hC₁⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
    s₂ u hs₂0 hu0 (D + (D + canonicalDivisorOf hω₀)) hD₂ hs₂D huD hbpf
  obtain ⟨C₂, hC₂⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_add_pointHt_le N s w s₂ hs0 hw0 hs₂0 D
    (D + canonicalDivisorOf hω₀) hD hDK hsD hwD hs₂D
  obtain ⟨C₀, hC₀⟩ := absLogHeight_reindex_le e he
  refine ⟨C₀ + C₁ + C₂, fun v t ht => ?_⟩

  obtain ⟨hy0, μ, hμ0, hev⟩ := evalVec_wronskian_family N x hx hr s hs0 D hD hsD ha0 (canonicalDivisorOf hω₀) hK
    hb e u hu hS hu0 v (hbpf v) ht
  set y : Fin r × Fin r → AlgebraicClosure ℚ := fun q =>
    regVal s v t 1 1 (evalVec s v q.1 • s q.2 - evalVec s v q.2 • s q.1) with hy_def
  have hpt : pointHt u v = absLogHeight (y ∘ e) := by
    show absLogHeight (evalVec u v) = _
    rw [hev, absLogHeight_smul _ hμ0]
  have h0 := hC₀ y hy0
  have h1 := hC₁ v
  have h2 := hC₂ v
  rw [hpt] at h1
  rw [abs_le] at h0 h1 h2 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

end BarT
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le.P2MW"

open AlgebraicCurve ModularCurve

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))]
    {r c : ℕ} (s : Fin r → ↥(ModularCurve.modularFunctionFieldBar N))
    (w : Fin c → ↥(ModularCurve.modularFunctionFieldBar N))
    (hs0 : ∀ i, s i ≠ 0) (hw0 : ∀ l, w l ≠ 0)
    (hg : 1 ≤ AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hD : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = AlgebraicCurve.riemannRochSpace D)
    {ω₀ : Ω[↥(ModularCurve.modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω₀ : ω₀ ≠ 0)
    (hwD : Submodule.span (AlgebraicClosure ℚ) (Set.range w)
      = AlgebraicCurve.riemannRochSpace (D + AlgebraicCurve.canonicalDivisorOf hω₀)) :
    ∃ C : ℝ, ∀ (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
      (t : ↥(ModularCurve.modularFunctionFieldBar N)), v.ord t = 1 →
      |AlgebraicCurve.absLogHeight (fun p : Fin r × Fin r =>
          AlgebraicCurve.regVal s v t 1 1
            (AlgebraicCurve.evalVec s v p.1 • s p.2 - AlgebraicCurve.evalVec s v p.2 • s p.1))
        - (AlgebraicCurve.pointHt s v + AlgebraicCurve.pointHt w v)| ≤ C :=
  P2MW.tangent_main N s w hs0 hw0 hg D hD hsD hω₀ hwD

end S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le
end P2MW
export P2MW.S_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le (solution)
