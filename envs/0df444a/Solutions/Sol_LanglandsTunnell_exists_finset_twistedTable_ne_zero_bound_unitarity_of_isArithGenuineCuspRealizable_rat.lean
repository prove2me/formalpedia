-- Prove2me | solution 1 for LanglandsTunnell.exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6a18f1fb-d59a-5e5f-909c-f15b00478674

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
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Theorems.Thm_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

namespace TableFactsRatSol

open NumberField.TateGlobal

theorem det_diagOne {A : Type*} [CommRing A] (z : Aˣ) :
    Matrix.GeneralLinearGroup.det (AdelicLevel.diagOne z) = z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    show ((AdelicLevel.diagOne z : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
        = Matrix.diagonal ![(z : A), 1] from rfl,
    Matrix.det_diagonal]
  simp

theorem det_heckeGen (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ v) = uniformizerIdele ℚ v := by
  show Matrix.GeneralLinearGroup.det
      (AdelicLevel.diagOne ((Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* _))
        (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v)))) = _
  rw [det_diagOne]
  rfl

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 ℚ)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  omega

theorem one_lt_absNormReal (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have := two_le_absNorm v
  exact_mod_cast this

theorem absNormReal_pos (v : HeightOneSpectrum (𝓞 ℚ)) :
    (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  zero_lt_one.trans (one_lt_absNormReal v)

section Central

variable (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
  (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

theorem xi_uniformizerIdele_eq
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S₀ Θ φ₀) (hne0 : φ₀ ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S₀) :
    (((ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (uniformizerIdele ℚ v) : ℂˣ) : ℂ)
      = (HeckeEigensystem.cNorm v)⁻¹ * Θ.b v := by
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne0

  have hA : IsAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₀ := hiso.smoothCusp.1.1
  have hL := (AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ ξ _ φ₀).mp hA
  set z : (productionPinsGeneral ℚ).Z := Subgroup.topEquiv.symm.toMonoidHom (uniformizerIdele ℚ v)
    with hz
  have hzval : ((z : (productionPinsGeneral ℚ).Z) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = uniformizerIdele ℚ v := rfl
  have h1 := hL.1.central_transform z g
  rw [hzval] at h1

  have h2 := hiso.central_eigen v hv g
  have hgen : (productionPinsGeneral ℚ).gen v = heckeGen (𝓞 ℚ) ℚ v := rfl
  rw [hgen, det_heckeGen] at h2
  rw [h1] at h2
  have h3 : ((ξ z : ℂˣ) : ℂ) = Θ.toRawCentral.b v := mul_right_cancel₀ hg h2
  rw [show (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (uniformizerIdele ℚ v) = ξ z from rfl, h3]
  rfl

theorem norm_b_eq
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S₀ Θ φ₀) (hne0 : φ₀ ≠ 0)
    (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S₀) :
    ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀) := by
  have h := hσ₀ (uniformizerIdele ℚ v)
  rw [xi_uniformizerIdele_eq Θ ξ S₀ φ₀ hiso hne0 v hv,
    NumberField.TateGlobal.ideleNorm_uniformizerIdele ℚ v, norm_mul, norm_inv] at h
  have hN : ‖HeckeEigensystem.cNorm v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    simp [HeckeEigensystem.cNorm]
  rw [hN] at h
  have hpos := absNormReal_pos v
  rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le, inv_mul_eq_iff_eq_mul₀ hpos.ne'] at h
  rw [h, sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one]

end Central

theorem a_mul_conj_b_eq {a b : ℂ} {t : ℝ} (ht : 0 ≤ t) (h : a ^ 2 = (t : ℂ) * b) :
    a * (starRingEnd ℂ) b = ((‖b‖ : ℝ) : ℂ) * (starRingEnd ℂ) a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  refine mul_right_cancel₀ ha ?_
  have hna : ‖a‖ ^ 2 = t * ‖b‖ := by
    rw [← norm_pow, h, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
  have e1 : a * (starRingEnd ℂ) b * a = (t : ℂ) * (b * (starRingEnd ℂ) b) := by
    rw [mul_right_comm, ← sq, h, mul_assoc]
  rw [e1, Complex.mul_conj', mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, hna]
  push_cast
  ring

theorem twisted_a_bound {a b : ℂ} {N σ₀ : ℝ} (hN : 2 ≤ N)
    (hb : ‖b‖ = N ^ (1 - σ₀)) (hlt : ‖a‖ ^ 2 < ‖b‖ * (N + 2 + N⁻¹)) :
    ‖(((N ^ (σ₀ / 2) : ℝ) : ℂ) * a)‖ ≤ N ^ (2 : ℝ) := by
  have hpos : 0 < N := by linarith
  have h1N : 1 ≤ N := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), Real.rpow_two]

  refine le_of_pow_le_pow_left₀ two_ne_zero (sq_nonneg _) ?_
  have hsq : (N ^ (σ₀ / 2) * ‖a‖) ^ 2 = N ^ σ₀ * ‖a‖ ^ 2 := by
    rw [mul_pow, sq (N ^ (σ₀ / 2)), ← Real.rpow_add hpos, add_halves]
  rw [hsq]
  have hinv : N⁻¹ ≤ N := (inv_le_one_of_one_le₀ h1N).trans h1N
  have h4 : N + 2 + N⁻¹ ≤ 4 * N := by linarith
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hle : ‖a‖ ^ 2 ≤ N ^ (1 - σ₀) * (4 * N) := by
    rw [← hb]
    exact hlt.le.trans (mul_le_mul_of_nonneg_left h4 hb0)
  have hσpos : 0 ≤ N ^ σ₀ := Real.rpow_nonneg hpos.le _
  calc N ^ σ₀ * ‖a‖ ^ 2 ≤ N ^ σ₀ * (N ^ (1 - σ₀) * (4 * N)) := mul_le_mul_of_nonneg_left hle hσpos
    _ = 4 * N ^ 2 := by
        rw [← mul_assoc, ← Real.rpow_add hpos, show σ₀ + (1 - σ₀) = 1 by ring, Real.rpow_one]
        ring
    _ ≤ (N ^ 2) ^ 2 := by
        have h4N : 4 ≤ N ^ 2 := by nlinarith
        nlinarith [sq_nonneg N]

theorem twisted_b_norm {b : ℂ} {N σ₀ : ℝ} (hpos : 0 < N) (hb : ‖b‖ = N ^ (1 - σ₀)) :
    ‖(((N ^ σ₀ : ℝ) : ℂ) * (b / (N : ℂ)))‖ = 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), norm_div,
    Complex.norm_real, Real.norm_of_nonneg hpos.le, hb, mul_div_assoc', ← Real.rpow_add hpos,
    show σ₀ + (1 - σ₀) = 1 by ring, Real.rpow_one, div_self hpos.ne']

end TableFactsRatSol

open TableFactsRatSol in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S₀ Θ φ₀) (hne0 : φ₀ ≠ 0)
    (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀) :
    ∃ S₅ : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₅ →
        (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))) ≠ 0) ∧
      (∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₅ →
        ‖(((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (σ₀ / 2) : ℝ) : ℂ) * Θ.a v)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖(((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)))‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₅ →
        Θ.a v * (starRingEnd ℂ) (Θ.b v) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀) : ℝ) : ℂ) * (starRingEnd ℂ) (Θ.a v) ∧
        ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀)) := by
  classical
  obtain ⟨S₁, hS₁⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
      ℚ c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
  have hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ ∪ S₁ →
      ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀) := fun v hv =>
    norm_b_eq Θ ξ S₀ φ₀ hiso hne0 σ₀ hσ₀ v (Finset.notMem_union.mp hv).1
  have hcast : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) := fun v => by
    push_cast; rfl
  refine ⟨S₀ ∪ S₁, fun v hv => ?_, ⟨2, fun v hv => ⟨?_, ?_⟩⟩, fun v hv => ⟨?_, hb v hv⟩⟩
  ·
    have hpos := absNormReal_pos v
    have hbv := hb v hv
    have hb0 : Θ.b v ≠ 0 := by
      rw [← norm_pos_iff, hbv]
      exact Real.rpow_pos_of_pos hpos _
    refine mul_ne_zero ?_ (div_ne_zero hb0 ?_)
    · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hpos _).ne'
    · rw [hcast]; exact Complex.ofReal_ne_zero.mpr hpos.ne'
  ·
    have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
    exact twisted_a_bound h2 (hb v hv) (hS₁ v (Finset.notMem_union.mp hv).2).2
  ·
    rw [hcast, twisted_b_norm (absNormReal_pos v) (hb v hv)]
    exact Real.one_le_rpow (one_lt_absNormReal v).le zero_le_two
  ·
    obtain ⟨t, ht, hsq⟩ := (hS₁ v (Finset.notMem_union.mp hv).2).1
    rw [← hb v hv]
    exact a_mul_conj_b_eq ht hsq

end S_LanglandsTunnell_exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat
end P2MW
export P2MW.S_LanglandsTunnell_exists_finset_twistedTable_ne_zero_bound_unitarity_of_isArithGenuineCuspRealizable_rat (solution)
