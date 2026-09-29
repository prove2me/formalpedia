-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/af9679ef-c23e-5cde-9a0e-4dc715c1ce5e

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add
import Theorems.Thm_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane Filter AlgebraicCurve
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary jq jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange isCurveOver_laurentBaseChange_modularFunctionFieldFull transcendental_coeffEmb_jq finiteDimensional_adjoin_coeffEmb_jq_full jqModC_eq_qExpansion_E4_cube_div_discriminant jqModC jqModC_rat map_jqModC realize_eq_div exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg"
namespace ComplexPlaceDictionary
p2m_export "ModularCurve.ComplexPlaceDictionary" "ramification pt mem_pt_iff exists_realize_mul_deriv_realize_eq_div_add"
namespace ResidueNeZeroAux
p2m_open "ModularCurve.ComplexPlaceDictionary ModularCurve"

variable (N : ℕ) [NeZero N]

abbrev CF : Type := ↥(laurentBaseChange ℂ (modularFunctionFieldFull N))

def Xj : CF N :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (modularFunctionField_le_full N (jq_mem N))⟩

@[scoped simp] theorem coe_Xj : ((Xj N : CF N) : LaurentSeries ℂ) = coeffEmb ℂ jq := rfl

theorem transcendental_Xj : Transcendental ℂ (Xj N) := transcendental_coeffEmb_jq ℂ N

scoped instance finiteDimensional_adjoin_Xj :
    FiniteDimensional (IntermediateField.adjoin ℂ ({Xj N} : Set (CF N))) (CF N) :=
  finiteDimensional_adjoin_coeffEmb_jq_full ℂ N

scoped instance essFiniteType_CF : Algebra.EssFiniteType ℂ (CF N) :=
  essFiniteType_of_transcendental_of_finiteDimensional (transcendental_Xj N)
    (finiteDimensional_adjoin_Xj N)

scoped instance isCurveOver_CF : IsCurveOver ℂ (CF N) :=
  isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N

scoped instance hasCanonicalDivisor_CF : HasCanonicalDivisor (K := ℂ) (F := CF N) :=
  hasCanonicalDivisor_of_isCurveOver

scoped instance dCoordGenerates_CF (w : Place ℂ (CF N)) : w.DCoordGenerates :=
  dCoordGenerates_of_isCurveOver w

theorem riemannRoch_CF : FunctionFieldRiemannRoch ℂ (CF N) :=
  functionFieldRiemannRoch_of_isAlgClosed_of_transcendental (transcendental_Xj N)
    (finiteDimensional_adjoin_Xj N)

section ModularForms

omit [NeZero N] in

theorem Gamma0_le_SL :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    {k : ℤ} (f : F) [ModularFormClass F Γ k] : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

@[scoped simp]
theorem coe_restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (hle : Γ' ≤ Γ) {k : ℤ} (f : F) [ModularFormClass F Γ k] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

def G : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  restrict (Gamma0_le_SL N) (ModularForm.mcast (by decide) (ModularForm.E₄.pow 3))

def H : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  restrict (Gamma0_le_SL N) CuspForm.discriminant

omit [NeZero N] in
theorem coe_G : ((G N : ModularForm _ 12) : ℍ → ℂ) =
    ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl

omit [NeZero N] in
theorem coe_H : ((H N : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

omit [NeZero N] in
theorem H_apply_ne_zero (z : ℍ) : (H N : ℍ → ℂ) z ≠ 0 := by
  rw [coe_H]
  exact ModularForm.discriminant_ne_zero z

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

omit [NeZero N] in
theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

omit [NeZero N] in
theorem continuous_coe {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    Continuous (f : ℍ → ℂ) :=
  (ModularFormClass.holo f).continuous

omit [NeZero N] in

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL N f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

omit [NeZero N] in
theorem H_ne_zero : H N ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 N) 12 => (f : ℍ → ℂ) I) h
  exact H_apply_ne_zero N I (by simpa using this)

omit [NeZero N] in
theorem qL_G : qL N (G N) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have h : qExpansion 1 ((G N : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [coe_G, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

omit [NeZero N] in
theorem qL_H : qL N (H N) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem coeffEmb_jq_eq : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℂ)

omit [NeZero N] in

theorem coeffEmb_jq_mul_qL_H : coeffEmb ℂ jq * qL N (H N) = qL N (G N) := by
  rw [coeffEmb_jq_eq, jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G, ← qL_H N]
  exact div_mul_cancel₀ _ (qL_ne_zero N (H N) (H_ne_zero N))

omit [NeZero N] in

theorem realize_coeffEmb_jq (z : ℍ) :
    realize N (coeffEmb ℂ jq) z = (G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z :=
  ModularCurve.realize_eq_div N (G N) (H N) (coeffEmb ℂ jq) (coeffEmb_jq_mul_qL_H N) z
    (H_apply_ne_zero N z)

omit [NeZero N] in

theorem isBoundedUnder_realize_coeffEmb_jq (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (coeffEmb ℂ jq) z‖) := by
  have hcont : Continuous (fun z : ℍ => (G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z) :=
    (continuous_coe N (G N)).div (continuous_coe N (H N)) (H_apply_ne_zero N)
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z‖) :=
    (hcont.continuousAt.norm.tendsto).isBoundedUnder_le
  have hfun : (fun z : ℍ => ‖realize N (coeffEmb ℂ jq) z‖) =
      fun z : ℍ => ‖(G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z‖ :=
    funext fun z => by rw [realize_coeffEmb_jq]
  rw [hfun]
  exact hbd.mono nhdsWithin_le_nhds

end ModularForms

theorem Xj_mem_pt (D : ComplexPlaceDictionary N) (τ : ℍ) :
    Xj N ∈ (D.pt τ).toValuationSubring :=
  (D.mem_pt_iff τ (Xj N)).mpr (isBoundedUnder_realize_coeffEmb_jq N τ)

omit [NeZero N] in

theorem realize_smul (x : LaurentSeries ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (τ : ℍ) : realize N x (γ • τ) = realize N x τ := by
  classical

  have law : ∀ {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (f : ℍ → ℂ) (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ k * (f : ℍ → ℂ) τ :=
    fun f => SlashInvariantForm.slash_action_eqn_SL'' f hγ τ
  have hd : ∀ k : ℤ, (denom (γ : GL (Fin 2) ℝ) τ : ℂ) ^ k ≠ 0 :=
    fun k => zpow_ne_zero _ (denom_ne_zero _ _)
  by_cases hex : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
        ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
  · obtain ⟨⟨k, g, h⟩, hτ, heq⟩ := hex
    have hγτ : (h : ℍ → ℂ) (γ • τ) ≠ 0 := by
      rw [law h]; exact mul_ne_zero (hd k) hτ
    rw [ModularCurve.realize_eq_div N g h x heq _ hγτ, ModularCurve.realize_eq_div N g h x heq _ hτ,
      law g, law h, mul_div_mul_left _ _ (hd k)]
  · have hex' : ¬ ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) (γ • τ) ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rintro ⟨p, hp, heq⟩
      refine hex ⟨p, ?_, heq⟩
      intro h0
      exact hp (by rw [law p.2.2, h0, mul_zero])
    unfold realize
    rw [dif_neg hex, dif_neg hex']

def μ (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)

omit [NeZero N] in
theorem μ_coe (g : SL(2, ℤ)) (τ : ℍ) : μ g τ = ((g • τ : ℍ) : ℂ) := by
  simp [μ, ofComplex_apply]

theorem hasDerivAt_μ (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (μ γ) (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ)) = μ γ := by
    funext z
    rw [μ, MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try first | with_reducible_and_instances rfl | rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem slash_two_apply (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) τ =
      f (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) :=
  ModularForm.SL_slash_apply f γ τ

theorem comp_μ_eq {f : ℍ → ℂ} {γ : SL(2, ℤ)} (hf : ∀ τ : ℍ, f (γ • τ) = f τ) :
    (fun w : ℂ => f (ofComplex w)) ∘ μ γ = fun w : ℂ => f (ofComplex w) := by
  funext z
  simp only [Function.comp_apply, μ, ofComplex_apply]
  exact hf _

theorem deriv_comp_ofComplex_smul {f : ℍ → ℂ} {γ : SL(2, ℤ)} (hf : ∀ τ : ℍ, f (γ • τ) = f τ)
    (τ : ℍ) :
    deriv (fun w : ℂ => f (ofComplex w)) ↑(γ • τ) *
        denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) =
      deriv (fun w : ℂ => f (ofComplex w)) ↑τ := by
  set F : ℂ → ℂ := fun w => f (ofComplex w) with hF
  have hf' : ∀ τ : ℍ, f (γ⁻¹ • τ) = f τ := fun τ => by
    conv_rhs => rw [← smul_inv_smul γ τ]
    exact (hf _).symm
  by_cases hd : DifferentiableAt ℂ F ↑(γ • τ)
  · have h1 : HasDerivAt F (deriv F ↑(γ • τ)) (μ γ ↑τ) := by
      rw [μ_coe]; exact hd.hasDerivAt
    have h2 := h1.comp ((τ : ℍ) : ℂ) (hasDerivAt_μ γ τ)
    rw [comp_μ_eq hf] at h2
    exact h2.deriv.symm
  · have hd' : ¬ DifferentiableAt ℂ F ↑τ := by
      intro hτ
      apply hd
      have h1 : DifferentiableAt ℂ F (μ γ⁻¹ ↑(γ • τ)) := by
        rwa [μ_coe, inv_smul_smul]
      have h2 := h1.comp (((γ • τ : ℍ)) : ℂ) (hasDerivAt_μ γ⁻¹ (γ • τ)).differentiableAt
      rwa [comp_μ_eq hf'] at h2
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', zero_mul]

omit [NeZero N] in

theorem eq_of_sub_algebraMap_mem_nonunits {F : Type*} [Field F] [Algebra ℂ F] (v : Place ℂ F)
    {y : F} {ρ ρ' : ℂ}
    (h : y - algebraMap ℂ F ρ ∈ v.toValuationSubring.nonunits)
    (h' : y - algebraMap ℂ F ρ' ∈ v.toValuationSubring.nonunits) : ρ = ρ' := by
  by_contra hne
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at h h'
  obtain ⟨hm, hmax⟩ := h
  obtain ⟨hm', hmax'⟩ := h'
  have hsub := Ideal.sub_mem _ hmax' hmax
  have hcalc : (⟨y - algebraMap ℂ F ρ', hm'⟩ : v.toValuationSubring) - ⟨y - algebraMap ℂ F ρ, hm⟩ =
      algebraMap ℂ v.toValuationSubring (ρ - ρ') := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap, map_sub]
    ring
  rw [hcalc] at hsub
  have hu : IsUnit (algebraMap ℂ v.toValuationSubring (ρ - ρ')) :=
    (IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _
  exact (IsLocalRing.mem_maximalIdeal _).mp hsub hu

theorem exists_slashInvariant_residue_ne_zero_of_pt_ne (D : ComplexPlaceDictionary N)
    {τ₁ τ₂ : ℍ} (hne : D.pt τ₁ ≠ D.pt τ₂) :
    ∃ (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) →₀ ℂ),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 N, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) ∧
      r (D.pt τ₁) ≠ 0 ∧
      (∀ P, r P ≠ 0 → P = D.pt τ₁ ∨ P = D.pt τ₂) ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z := by
  classical

  obtain ⟨θ, hθ0, hP, hQ, hrest⟩ :=
    AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne (K := ℂ) (F := CF N)
      (riemannRoch_CF N) hne

  obtain ⟨a, ha, -⟩ :=
    KaehlerDifferential.exists_unique_smul_D_of_transcendental ℂ (Xj N) (transcendental_Xj N) θ

  have hord : ∀ τ : ℍ, -1 ≤ (D.pt τ).ordDifferential θ := by
    intro τ
    by_cases h1 : D.pt τ = D.pt τ₁
    · rw [h1, hP]
    by_cases h2 : D.pt τ = D.pt τ₂
    · rw [h2, hQ]
    have := hrest _ h1 h2
    omega

  have loc : ∀ τ : ℍ, ∃ (ρ : ℂ) (g : ℂ → ℂ),
      (D.pt τ).differentialCoeff θ * (D.pt τ).uniformizer - algebraMap ℂ (CF N) ρ ∈
        (D.pt τ).toValuationSubring.nonunits ∧
      (ρ ≠ 0 ↔ (D.pt τ).ordDifferential θ = -1) ∧
      AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        realize N (a : LaurentSeries ℂ) (ofComplex z) *
            deriv (fun w : ℂ => realize N ((Xj N : CF N) : LaurentSeries ℂ) (ofComplex w)) z =
          (D.ramification τ : ℂ) * ρ / (z - τ) + g z :=
    fun τ => D.exists_realize_mul_deriv_realize_eq_div_add a (Xj N) (D.pt τ).uniformizer τ θ ha
      hθ0 (hord τ) (D.pt τ).ord_uniformizer (D.pt τ).dCoord_eq
  choose ρ g hnu hiff han hloc using loc

  have hρ : ∀ τ τ' : ℍ, D.pt τ = D.pt τ' → ρ τ = ρ τ' := by
    intro τ τ' hpt
    have h1 := hnu τ
    have h2 := hnu τ'
    rw [← hpt] at h2
    exact eq_of_sub_algebraMap_mem_nonunits _ h1 h2

  refine ⟨fun τ : ℍ => realize N (a : LaurentSeries ℂ) τ *
      deriv (fun w : ℂ => realize N ((Xj N : CF N) : LaurentSeries ℂ) (ofComplex w)) τ,
    Finsupp.single (D.pt τ₁) (ρ τ₁) + Finsupp.single (D.pt τ₂) (ρ τ₂),
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro γ hγ
    funext τ
    rw [slash_two_apply, realize_smul N _ hγ, mul_assoc,
      deriv_comp_ofComplex_smul (fun τ' => realize_smul N ((Xj N : CF N) : LaurentSeries ℂ) hγ τ')]
  ·
    intro σ
    refine exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg N a
      (Xj N) (fun v hv => ?_) σ
    have h1 : v ≠ D.pt τ₁ := fun h => hv (h ▸ Xj_mem_pt N D τ₁)
    have h2 : v ≠ D.pt τ₂ := fun h => hv (h ▸ Xj_mem_pt N D τ₂)
    simpa [ha] using hrest v h1 h2
  ·
    have h : (Finsupp.single (D.pt τ₁) (ρ τ₁) + Finsupp.single (D.pt τ₂) (ρ τ₂)) (D.pt τ₁) =
        ρ τ₁ := by
      simp [Ne.symm hne]
    rw [h]
    exact (hiff τ₁).mpr hP
  ·
    intro v hv
    by_contra hcon
    push Not at hcon
    apply hv
    simp [Ne.symm hcon.1, Ne.symm hcon.2]
  ·
    intro τ
    refine ⟨g τ, han τ, ?_⟩
    have hval : (Finsupp.single (D.pt τ₁) (ρ τ₁) + Finsupp.single (D.pt τ₂) (ρ τ₂)) (D.pt τ) =
        ρ τ := by
      by_cases h1 : D.pt τ = D.pt τ₁
      · rw [hρ τ τ₁ h1, h1]
        simp [Ne.symm hne]
      by_cases h2 : D.pt τ = D.pt τ₂
      · rw [hρ τ τ₂ h2, h2]
        simp [hne]
      have h0 : ρ τ = 0 := by
        by_contra hρ0
        have := (hiff τ).mp hρ0
        have := hrest _ h1 h2
        omega
      rw [h0]
      simp [Ne.symm h1, Ne.symm h2]
    have him : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
      mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    filter_upwards [hloc τ, him] with z hz hzim
    rw [hval, ← hz, ofComplex_apply_of_im_pos hzim]

end ModularCurve.ComplexPlaceDictionary.ResidueNeZeroAux
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve.ComplexPlaceDictionary P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve.ComplexPlaceDictionary.ResidueNeZeroAux"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve.ComplexPlaceDictionary"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve"

open ModularCurve.ComplexPlaceDictionary.ResidueNeZeroAux in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) {τ₁ τ₂ : ℍ}
    (hne : D.pt τ₁ ≠ D.pt τ₂) :
    ∃ (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) →₀ ℂ),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 N, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) ∧
      r (D.pt τ₁) ≠ 0 ∧
      (∀ P, r P ≠ 0 → P = D.pt τ₁ ∨ P = D.pt τ₂) ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z :=
  exists_slashInvariant_residue_ne_zero_of_pt_ne N D hne

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve.ComplexPlaceDictionary P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne.ModularCurve.ComplexPlaceDictionary.ResidueNeZeroAux"

end S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_ne_zero_of_pt_ne (solution)
