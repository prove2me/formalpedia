-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8992c2db-7651-5754-a4e9-ed185e99777a

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_expansion_of_casimir_relations
import Theorems.Thm_LanglandsTunnell_CubicInduction_coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_conditions_foldr_archDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCuspidalAlong_foldr_archDeriv_sum_translate
import Theorems.Thm_LanglandsTunnell_CubicInduction_isRightInvariant_foldr_archDeriv_sum_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

set_option autoImplicit false

open LanglandsTunnell.CubicInduction

noncomputable section

namespace RayCore48

def ContCoeff (n J : ℕ) (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}

def HasExp1 (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (n J : ℕ) (e : Fin n → ℂ) (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (τ : ℝ) : Prop :=
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ

theorem aut_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑ i, c i * f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g * t i) = ∑ i, c i * f (g * t i) := by
  simp only [mul_assoc, haut]

theorem cen_sum_translate (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑ i, c i * f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g * t i) = (ω z : ℂ) * ∑ i, c i * f (g * t i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc (centralScalarGL 3 (𝓞 ℚ) ℚ z), hcen]
  ring

theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {n : ℕ} (c : Fin n → ℂ)
    (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (hsm : ∀ i, WhittakerBlock.IsArchSmooth3 fun x => f (x * t i)) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsm i g)

theorem kfinite_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => ∑ i, c i * f (g * k * t i)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hKf
  refine ⟨Finset.univ.biUnion fun i => s.image fun φ g => φ (g * t i), fun k hkf hka => ?_⟩
  have hrew : (fun g => ∑ i, c i * f (g * k * t i)) =
      ∑ i, c i • LinearMap.funLeft ℂ ℂ (fun g => g * t i) (fun g => f (g * ((t i)⁻¹ * k * t i))) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show g * k * t i = g * t i * ((t i)⁻¹ * k * t i) by group]
  rw [hrew]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hk' : (fun g => f (g * ((t i)⁻¹ * k * t i))) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
    refine hs _ (fun p => ?_) ?_
    · simp [map_mul, map_inv, hkf p]
    · simpa [map_mul, map_inv, ht i] using hka
  refine Submodule.span_mono ?_
    (Submodule.apply_mem_span_image_of_mem_span (LinearMap.funLeft ℂ ℂ fun g => g * t i) hk')
  rintro _ ⟨φ, hφ, rfl⟩
  exact Finset.mem_coe.2
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem (fun φ g => φ (g * t i)) hφ⟩)

theorem exists_isCompact_mem_interior (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ∃ B : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact B ∧ k ∈ interior B := by
  obtain ⟨B, hB, hkB⟩ := exists_compact_mem_nhds k
  exact ⟨B, hB, mem_interior_iff_mem_nhds.mpr hkB⟩

theorem sum_reindex {n J m : ℕ} (e : Fin n → ℂ) (e' : Fin m → ℂ) (he' : Function.Injective e')
    (hsur : ∀ i, ∃ i', e' i' = e i) (a : Fin n → Fin J → ℂ) (X : ℂ → Fin J → ℂ) :
    ∑ i' : Fin m, ∑ j : Fin J, (∑ i : Fin n, if e i = e' i' then a i j else 0) * X (e' i') j =
      ∑ i : Fin n, ∑ j : Fin J, a i j * X (e i) j := by
  classical
  have hswap : ∑ i' : Fin m, ∑ j : Fin J, (∑ i : Fin n, if e i = e' i' then a i j else 0) * X (e' i') j =
      ∑ i : Fin n, ∑ j : Fin J, ∑ i' : Fin m, (if e i = e' i' then a i j else 0) * X (e' i') j := by
    calc ∑ i' : Fin m, ∑ j : Fin J, (∑ i : Fin n, if e i = e' i' then a i j else 0) * X (e' i') j
        = ∑ i' : Fin m, ∑ j : Fin J, ∑ i : Fin n, (if e i = e' i' then a i j else 0) * X (e' i') j := by
          refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ i' : Fin m, ∑ i : Fin n, ∑ j : Fin J, (if e i = e' i' then a i j else 0) * X (e' i') j := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ i' : Fin m, ∑ j : Fin J, (if e i = e' i' then a i j else 0) * X (e' i') j := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin J, ∑ i' : Fin m, (if e i = e' i' then a i j else 0) * X (e' i') j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨i₀, hi₀⟩ := hsur i
  rw [Finset.sum_eq_single i₀]
  · rw [if_pos hi₀.symm, hi₀]
  · intro i' _ hi'
    have hne : e i ≠ e' i' := fun h => hi' (he' (h.symm.trans hi₀.symm))
    rw [if_neg hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

theorem merge (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (n J : ℕ) (e : Fin n → ℂ) (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (τ : ℝ)
    (hcont : ContCoeff n J c) (hexp : HasExp1 F n J e c τ) :
    ∃ (m : ℕ) (e' : Fin m → ℂ) (c' : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Function.Injective e' ∧ (∀ i', ∃ i, e' i' = e i) ∧ ContCoeff m J c' ∧ HasExp1 F m J e' c' τ := by
  classical
  set s : Finset ℂ := Finset.univ.image e with hs
  set φ := s.equivFin with hφ
  have he' : Function.Injective (fun i' : Fin s.card => ((φ.symm i' : ↥s) : ℂ)) :=
    fun a b hab => φ.symm.injective (Subtype.ext hab)
  have hsur : ∀ i : Fin n, ∃ i' : Fin s.card, ((φ.symm i' : ↥s) : ℂ) = e i := by
    intro i
    have hm : e i ∈ s := by rw [hs]; exact Finset.mem_image_of_mem e (Finset.mem_univ i)
    refine ⟨φ ⟨e i, hm⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
  refine ⟨s.card, fun i' => ((φ.symm i' : ↥s) : ℂ),
    fun i' j y k => ∑ i, if e i = ((φ.symm i' : ↥s) : ℂ) then c i j y k else 0, he', ?_, ?_, ?_⟩
  · intro i'
    have hm : ((φ.symm i' : ↥s) : ℂ) ∈ Finset.univ.image e := by
      rw [← hs]; exact (φ.symm i').2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, hi.symm⟩
  · intro i' j
    refine continuousOn_finsetSum _ fun i _ => ?_
    by_cases h : e i = ((φ.symm i' : ↥s) : ℂ)
    · simp only [if_pos h]; exact hcont i j
    · simp only [if_neg h]; exact continuousOn_const
  · intro K hK b hb
    obtain ⟨C, hC⟩ := hexp K hK b hb
    refine ⟨C, fun k hk y₂ hy₂ hy₂' y₁ hy₁ hy₁' => ?_⟩
    have key := sum_reindex e (fun i' => ((φ.symm i' : ↥s) : ℂ)) he' hsur (fun i j => c i j y₂ k)
      (fun z j => (y₁ : ℂ) ^ z * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))
    rw [key]
    exact hC k hk y₂ hy₂ hy₂' y₁ hy₁ hy₁'

end RayCore48

end

open RayCore48 in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∃ θ₀ : ℝ, 1 / 2 < θ₀ ∧
      ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous f →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g) →
      IsModerateGrowth3 ℚ f →
      IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f →
      IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f →
      ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) →
      WhittakerBlock.IsArchSmooth3 f →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ), (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) →
      IsCentreFinite (fun x => ∑ i, c i * f (x * t i)) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] fun x => ∑ i, c i * f (x * t i)) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] fun x => ∑ i, c i * f (x * t i)) = 0) →
      ∀ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      ∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ
            (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * h)‖ ≤
          C * y₁ ^ θ₀ := by
  classical

  obtain ⟨n₀, J, e, δ, hδ, hRe, H⟩ :=
    LanglandsTunnell.CubicInduction.exists_exponents_whittaker3_diag_expansion_of_casimir_relations
      ω N₂ a₂ ha₂ N₃ a₃ ha₃ (1 / 2)
  refine ⟨1 / 2 + δ, by linarith, ?_⟩

  intro f hc haut hcen hmg hP21 hP12 S hK hsm hsa hKf n c t ht hz hrel₂ hrel₃ w h
  have hτ : (1 : ℝ) / 2 < 1 / 2 + δ := by linarith

  have hgw :=
    LanglandsTunnell.CubicInduction.continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
      f hc hmg hsa hKf n c t ht hz
  obtain ⟨hvw, N, hvgr⟩ := hgw
  have hsmv : WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) :=
    isArchSmooth3_sum_translate f c t fun i => LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right f hsa (t i)
  have hautv : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (fun x => ∑ i, c i * f (x * t i)) (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = (fun x => ∑ i, c i * f (x * t i)) g :=
    fun γ g => aut_sum_translate f haut c t γ g
  have hcenv : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (fun x => ∑ i, c i * f (x * t i)) (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * (fun x => ∑ i, c i * f (x * t i)) g :=
    fun z g => cen_sum_translate ω f hcen c t z g
  have hKfv := kfinite_sum_translate f hKf c t ht

  set u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
    List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w with hu_def
  have hblk := LanglandsTunnell.CubicInduction.conditions_foldr_archDeriv N N₂ N₃ ω
    (fun x => ∑ i, c i * f (x * t i)) hautv hcenv hsmv hKfv ⟨a₂, ha₂, hrel₂⟩ ⟨a₃, ha₃, hrel₃⟩ hvgr hvw w u hu_def.symm
  obtain ⟨u_aut, u_cen, u_sa, u_Kf, -, -, u_gr, u_cw, u_tr₂, u_tr₃⟩ := hblk
  have u_rel₂ := u_tr₂ a₂ hrel₂
  have u_rel₃ := u_tr₃ a₃ hrel₃
  have u_cont : Continuous u := by simpa using u_cw []

  obtain ⟨⟨cc, hcont, hexp⟩, -⟩ := H N u u_cw u_aut u_cen u_sa u_Kf u_rel₂ u_rel₃ u_gr

  obtain ⟨m, e', c', he', he'e, hcont', hexp'⟩ := merge u n₀ J e cc (1 / 2 + δ) hcont hexp
  have hRe' : ∀ i', (e' i').re ≤ 1 / 2 := fun i' => by obtain ⟨i, hi⟩ := he'e i'; rw [hi]; exact hRe i

  have hcuspu := LanglandsTunnell.CubicInduction.isCuspidalAlong_foldr_archDeriv_sum_translate
    f hc hmg hP21 hP12 hsa hKf n c t ht hz w
  obtain ⟨S', hK', hsm'⟩ :=
    LanglandsTunnell.CubicInduction.isRightInvariant_foldr_archDeriv_sum_translate f S hK hsm n c t w

  have hkill : ∀ (i' : Fin m) (j : Fin J), ((e' i').re < 1 / 2 ∨ ((e' i').re = 1 / 2 ∧ 1 ≤ (j : ℕ))) →
      ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, c' i' j y₂ k = 0 := by
    intro i' j hij y₂ hy₂ k
    obtain ⟨B, hB, hkB⟩ := exists_isCompact_mem_interior k
    obtain ⟨Φ, φ₀, hφ₀, hΦ, hZ⟩ :=
      LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
        ω hω u u_cont u_aut u_cen hcuspu.1 hcuspu.2 S' hK' hsm' u_sa u_Kf u_cw N u_gr B hB 2 (by norm_num)
    exact LanglandsTunnell.CubicInduction.coeff_eq_zero_of_re_le_one_half_of_lintegral_torus_whittaker3_sq_le
      u m J e' he' c' hcont' (1 / 2 + δ) hτ hexp' B Φ 2 (by norm_num) φ₀ hφ₀ hΦ hZ i' j hij y₂ hy₂ k hkB

  have hu_span : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * f (g * h * t i)) w} := by
    refine Submodule.subset_span ⟨w, 1, ?_⟩
    simp only [mul_one]
    exact hu_def.symm
  have hhalf : ∀ (i' : Fin m), (e' i').re = 1 / 2 → ∀ j : Fin J, (j : ℕ) = 0 →
      ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, c' i' j y₂ k = 0 := by
    intro i' hD
    exact LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate
      ω hω f hc haut hcen hmg hP21 hP12 hsa hKf n c t ht hz u hu_span m J e' he' c' hcont' (1 / 2 + δ) hτ hexp'
      i' hD (fun i j hi => hkill i j (Or.inl hi)) (fun j hj => hkill i' j (Or.inr ⟨hD, hj⟩))

  have hall : ∀ (i' : Fin m) (j : Fin J) (y₂ : ℝ), 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, c' i' j y₂ k = 0 := by
    intro i' j y₂ hy₂ k
    rcases (hRe' i').lt_or_eq with hlt | heq
    · exact hkill i' j (Or.inl hlt) y₂ hy₂ k
    · by_cases hj : 1 ≤ (j : ℕ)
      · exact hkill i' j (Or.inr ⟨heq, hj⟩) y₂ hy₂ k
      · exact hhalf i' heq j (by omega) y₂ hy₂ k

  intro y₂ hy₂
  set b : ℝ := max (max y₂ y₂⁻¹) 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  obtain ⟨C, hC⟩ := hexp' {h} isCompact_singleton b hb1
  refine ⟨C, fun y₁ hy₁ hy₁1 => ?_⟩
  have hy₂b : y₂ ≤ b := (le_max_left _ _).trans (le_max_left _ _)
  have hy₂b' : b⁻¹ ≤ y₂ := by
    have : y₂⁻¹ ≤ b := (le_max_right _ _).trans (le_max_left _ _)
    rw [inv_le_comm₀ (lt_of_lt_of_le one_pos hb1) hy₂]
    exact this
  have key := hC h (Set.mem_singleton h) y₂ hy₂b' hy₂b y₁ hy₁ hy₁1
  have hzero : (∑ i : Fin m, ∑ j : Fin J, c' i j y₂ h * ((y₁ : ℂ) ^ e' i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hall i j y₂ hy₂ h, zero_mul]
  rw [hzero, sub_zero] at key
  simpa [hu_def] using key

end S_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant (solution)
