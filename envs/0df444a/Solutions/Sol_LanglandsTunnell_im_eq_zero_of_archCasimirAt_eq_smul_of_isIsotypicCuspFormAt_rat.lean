-- Prove2me | solution 1 for LanglandsTunnell.im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b8625507-f453-5c57-b38e-ddf744a6a4aa

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

import Theorems.Thm_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_archDerivAt_and_exists_bound_slab_of_isIsotypicCuspFormAt_of_rightConv_eq_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent

open _root_.LanglandsTunnell.RealArchParam in

open scoped ComplexConjugate in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hne0 : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (lam : ℂ) (hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ)
    (hΩ : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = lam • φ) :
    lam.im = 0 := by
  classical
  have hw : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

  obtain ⟨T, c, hc, u, hcov⟩ := AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet ℚ
  obtain ⟨d₁', d₂', tset, 𝓕, -, h𝓕m, h𝓕s, h𝓕, -⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
      ℚ c u 1 2 T hc one_pos one_lt_two (hcov 1 2 two_pos one_le_two) 1 2 one_pos one_lt_two

  obtain ⟨-, hD1, hD2, B, hB⟩ :=
    AutomorphicForm.continuous_archDerivAt_and_exists_bound_slab_of_isIsotypicCuspFormAt_of_rightConv_eq_rat
      ξ N S Θ φ hφ hconv 1 2 one_pos one_lt_two

  have hLs : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ φ :=
    ((AutomorphicForm.lsXiMemberAt_iff _ _ _ _ _ _ _).mp hφ.smoothCusp.1.1).1
  have hleft : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g :=
    hLs.left_invariant

  have hsym := (AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    ℚ default hw 1 2 one_pos one_lt_two 𝓕 h𝓕m h𝓕s h𝓕 φ φ hleft hleft hφ.continuous hφ.continuous hsm hsm hD1 hD1 hD2 hD2
    B (fun g hg => ⟨(hB g hg).1, (hB g hg).1, fun d => ⟨(hB g hg).2.1 d, (hB g hg).2.1 d⟩,
      fun d d' => ⟨(hB g hg).2.2 d d', (hB g hg).2.2 d d'⟩⟩)).1

  have hfin : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ 𝓕 < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain ℚ 1 2 one_pos one_lt_two 𝓕 h𝓕
    rwa [Set.inter_eq_self_of_subset_left h𝓕s] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  have hφ2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict 𝓕) := by
    refine MemLp.of_bound hφ.continuous.aestronglyMeasurable B ?_
    rw [ae_restrict_iff' h𝓕m]
    exact ae_of_all _ fun g hg => (hB g (h𝓕s hg)).1
  have hne := AutomorphicForm.setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
    ℚ 1 2 one_pos one_lt_two 𝓕 h𝓕s h𝓕 ξ 0 φ hLs hφ.continuous hφ2 hne0
  have hpt : (fun x : AdelicGL2 (𝓞 ℚ) ℚ => φ x * conj (φ x) *
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) ^ (-(0 : ℝ)) : ℝ) : ℂ))
      = fun x => φ x * conj (φ x) := by
    funext x
    rw [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  rw [hpt] at hne

  rw [hΩ] at hsym
  have h1 : ∫ g in 𝓕, (lam • φ) g * conj (φ g) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
      = lam * ∫ g in 𝓕, φ g * conj (φ g) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h2 : ∫ g in 𝓕, φ g * conj ((lam • φ) g) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
      = conj lam * ∫ g in 𝓕, φ g * conj (φ g) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  rw [h1, h2] at hsym
  have hlam : lam = conj lam := mul_right_cancel₀ hne hsym
  exact Complex.conj_eq_iff_im.mp hlam.symm

end S_LanglandsTunnell_im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat
end P2MW
export P2MW.S_LanglandsTunnell_im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat (solution)
