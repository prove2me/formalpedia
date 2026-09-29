-- Prove2me | solution 1 for ModularCurve.JZero.diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d4b2e4de-4bc7-53c2-bfcb-be0a106b285b

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero
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
p2m_reactivate "P2MW.S_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero.P2MW"

namespace P2MW

open AlgebraicCurve ModularCurve KaehlerDifferential

section BarW

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

theorem ratio_mem {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j))
    (i : Fin r) : s i * (s p)⁻¹ ∈ w.toValuationSubring :=
  w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 p)))
    (by rw [w.ord_mul (hs0 i) (inv_ne_zero (hs0 p)), w.ord_inv]; linarith [hp i])

theorem exists_evalAt_der_ne_zero (x' : modularFunctionFieldBar N)
    [FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ Divisor.degree D)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {t : modularFunctionFieldBar N} (ht : w.ord t = 1)
    (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j)) :
    ∃ j, w.evalAt (der (AlgebraicClosure ℚ) t (s j * (s p)⁻¹)) ≠ 0 := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  have hw := isRational_bar N w
  have hDt := D_ne_zero_of_ord_eq_one x' w ht
  have hsmem : ∀ i, s i ∈ riemannRochSpace D := mem_of_span_eq s hsD
  have hbpf := bpf_of_span_eq N s hsD (by omega) w
  have hordp : w.ord (s p) = -D w := ord_eq_neg_of_forall_le s hs0 hsmem w hbpf p hp
  have hdeg1 : Divisor.degree (D - Finsupp.single w 1) = Divisor.degree D - 1 := by
    rw [map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N w]; push_cast; ring
  obtain ⟨h, hh, hh'⟩ := exists_mem_notMem_bar N (D - Finsupp.single w 1) (by rw [hdeg1]; omega) w
  have hordh := ord_eq_of_mem_notMem w hh hh'
  rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at hordh
  have hh0 : h ≠ 0 := ne_zero_of_notMem hh'
  have hhD : h ∈ riemannRochSpace D := by
    refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_) hh
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hspan : h ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := hsD ▸ hhD
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hspan
  have hg : h * (s p)⁻¹ = ∑ i, c i • (s i * (s p)⁻¹) := by
    rw [← hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc]
  have hordg : w.ord (h * (s p)⁻¹) = 1 := by
    rw [w.ord_mul hh0 (inv_ne_zero (hs0 p)), w.ord_inv, hordp]; omega
  have hne := evalAt_der_ne_zero_of_ord_eq_one x' w hw ht hordg
  rw [hg, der_sum_smul hDt, evalAt_sum_smul_of_mem _ w hw c
    (fun i => der_mem x' w ht (ratio_mem N s hs0 w p hp i))] at hne
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨j, fun h0 => hj (by rw [h0, mul_zero])⟩

theorem nsmul_two_add_apply (D K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : (2 • D + K₀) w = 2 * D w + K₀ w := by
  rw [two_nsmul, Finsupp.add_apply, Finsupp.add_apply]; ring

theorem wronskian_main {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ Divisor.degree D)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    {x : modularFunctionFieldBar N} (hx : KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) x ≠ 0) :
    (∀ i j, Place.diffCoeff x (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s i))
        ∈ riemannRochSpace (2 • D + canonicalDivisorOf hx)) ∧
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i j,
      Place.diffCoeff x (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s i)) ≠ 0 ∧
      w.ord (Place.diffCoeff x (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s i)))
        + (2 • D + canonicalDivisorOf hx) w = 0 := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  obtain ⟨x', -, hx'fd, -⟩ :=
    IsCurveOver.exists_separating_transcendental (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)
  haveI := hx'fd
  have hr : 0 < r := pos_of_span_eq N s hsD (by omega)
  have hsmem : ∀ i, s i ∈ riemannRochSpace D := mem_of_span_eq s hsD
  refine ⟨fun i j => ?_, fun w => ?_⟩
  · rw [mem_riemannRochSpace_iff]
    intro w
    obtain ⟨t, ht⟩ := exists_ord_eq_one w
    obtain ⟨p, hp⟩ := exists_forall_ord_le hr s w
    have hordp : -D w ≤ w.ord (s p) := ((mem_riemannRochSpace_iff.mp (hsmem p)) w).resolve_left (hs0 p)
    have key := diffCoeff_wr_zero_or_le x' w ht hx (hs0 p) hordp (ratio_mem N s hs0 w p hp i)
      (ratio_mem N s hs0 w p hp j)
    rw [nsmul_two_add_apply]
    exact key
  · obtain ⟨t, ht⟩ := exists_ord_eq_one w
    obtain ⟨p, hp⟩ := exists_forall_ord_le hr s w
    have hw := isRational_bar N w
    have hDt := D_ne_zero_of_ord_eq_one x' w ht
    have hdx0 : der (AlgebraicClosure ℚ) t x ≠ 0 := der_ne_zero_of_chain hDt hx
    obtain ⟨j, hj⟩ := exists_evalAt_der_ne_zero N x' s hs0 hD hsD w ht p hp
    have hbpf := bpf_of_span_eq N s hsD (by omega) w
    have hordp : w.ord (s p) = -D w := ord_eq_neg_of_forall_le s hs0 hsmem w hbpf p hp
    have key := diffCoeff_mul_der_eq x' w ht hx (s p) (s j) (s p) (hs0 p)
    rw [mul_inv_cancel₀ (hs0 p), wr_one_left hDt] at key
    set W := Place.diffCoeff x (s p • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (s p)) with hW
    have hdj0 : der (AlgebraicClosure ℚ) t (s j * (s p)⁻¹) ≠ 0 := ne_zero_of_evalAt_ne_zero w hj
    have hordj : w.ord (der (AlgebraicClosure ℚ) t (s j * (s p)⁻¹)) = 0 :=
      ord_eq_zero_of_evalAt_ne_zero w hw (der_mem x' w ht (ratio_mem N s hs0 w p hp j)) hj
    have hrhs : (s p) ^ 2 * der (AlgebraicClosure ℚ) t (s j * (s p)⁻¹) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (hs0 p)) hdj0
    have hW0 : W ≠ 0 := by
      intro h0; rw [h0, zero_mul] at key; exact hrhs key.symm
    refine ⟨p, j, hW0, ?_⟩
    have h1 : w.ord W + w.ord (der (AlgebraicClosure ℚ) t x) = 2 * w.ord (s p) := by
      rw [← w.ord_mul hW0 hdx0, key, w.ord_mul (pow_ne_zero 2 (hs0 p)) hdj0, hordj, pow_two,
        w.ord_mul (hs0 p) (hs0 p)]; ring
    rw [ord_der_eq_canonical x' w ht hx, hordp] at h1
    rw [nsmul_two_add_apply]
    linarith

end BarW
p2m_reactivate "P2MW.S_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero.P2MW"

open AlgebraicCurve ModularCurve

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))]
    {r : ℕ} (s : Fin r → ↥(ModularCurve.modularFunctionFieldBar N)) (hs0 : ∀ i, s i ≠ 0)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hD : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = AlgebraicCurve.riemannRochSpace D)
    {x : ↥(ModularCurve.modularFunctionFieldBar N)}
    (hx : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) x ≠ 0) :
    (∀ i j, AlgebraicCurve.Place.diffCoeff x
        (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) (s i))
        ∈ AlgebraicCurve.riemannRochSpace (2 • D + AlgebraicCurve.canonicalDivisorOf hx)) ∧
    ∀ w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N), ∃ i j,
      AlgebraicCurve.Place.diffCoeff x
        (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) (s i)) ≠ 0 ∧
      w.ord (AlgebraicCurve.Place.diffCoeff x
        (s i • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) (s j)
          - s j • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) (s i)))
        + (2 • D + AlgebraicCurve.canonicalDivisorOf hx) w = 0 :=
  P2MW.wronskian_main N s hs0 D hD hsD hx

end S_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero
end P2MW
export P2MW.S_ModularCurve_JZero_diffCoeff_wronskian_mem_riemannRochSpace_and_exists_ord_add_eq_zero (solution)
