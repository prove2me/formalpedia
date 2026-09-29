-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e7cbc1d9-d481-567e-9cc2-378853d28d41

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_stable_translateRight_smoothingOperator
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ : IsSlabDomain a b Φ₀)
    (V₀ : Submodule ℂ (Carrier a b Φ₀))
    (_hgen : V₀ = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V₀})).topologicalClosure)
    (_hne : V₀ ≠ ⊥)
    (_htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V₀)
    (_hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V₀) :
    ∃ V : Submodule ℂ (Carrier a b Φ₀), V ≤ V₀ ∧
      V = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure ∧
      V ≠ ⊥ ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V) ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) ∧
      (∀ W : Submodule ℂ (Carrier a b Φ₀), W ≤ V →
        W = (Submodule.span ℂ
          (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ W})).topologicalClosure →
        (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
          ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
            toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ W) →
        (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
          ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
            ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
              toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ W) →
        W = ⊥ ∨ W = V) := by
  classical

  obtain ⟨hle₀, hWc, hWi⟩ :=
    le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap ω _hω a b Φ₀ _hΦ V₀ _hgen _htr
      _hsm (V₀.comap (cuspidalSubspace ω a b Φ₀).subtype) rfl
  have hWne : V₀.comap (cuspidalSubspace ω a b Φ₀).subtype ≠ ⊥ := by
    intro h
    apply _hne
    rw [eq_bot_iff]
    intro v hv
    have hvH : v ∈ cuspidalSubspace ω a b Φ₀ := hle₀ hv
    have hmem : (⟨v, hvH⟩ : ↥(cuspidalSubspace ω a b Φ₀)) ∈ V₀.comap (cuspidalSubspace ω a b Φ₀).subtype := hv
    rw [h, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val hmem

  obtain ⟨W₀, hW₀le, hW₀c, hW₀i, hW₀ne, hW₀min⟩ :=
    exists_le_minimal_of_isClosed_of_invariant_spectralOperators3 ω _hω a b Φ₀ _hΦ _ hWc hWi hWne

  obtain ⟨hgen, htr, hsm⟩ :=
    eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3 ω _hω a b Φ₀ _hΦ W₀ hW₀c hW₀i
      (W₀.map (cuspidalSubspace ω a b Φ₀).subtype) rfl
  refine ⟨W₀.map (cuspidalSubspace ω a b Φ₀).subtype, ?_, hgen, ?_, htr, hsm, ?_⟩
  ·
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    exact hW₀le hw
  ·
    intro h
    apply hW₀ne
    rw [eq_bot_iff]
    intro w hw
    have hmem : (cuspidalSubspace ω a b Φ₀).subtype w ∈ W₀.map (cuspidalSubspace ω a b Φ₀).subtype :=
      Submodule.mem_map_of_mem hw
    rw [h, Submodule.mem_bot] at hmem
    rw [Submodule.mem_bot]
    exact Subtype.ext hmem
  ·
    intro W' hW'le hgen' htr' hsm'
    obtain ⟨hle', hWc', hWi'⟩ :=
      le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap ω _hω a b Φ₀ _hΦ W' hgen' htr'
        hsm' (W'.comap (cuspidalSubspace ω a b Φ₀).subtype) rfl
    have hsub : W'.comap (cuspidalSubspace ω a b Φ₀).subtype ≤ W₀ := by
      intro w hw
      obtain ⟨w₀, hw₀, heq⟩ := Submodule.mem_map.mp (hW'le hw)
      have hww : w₀ = w := Subtype.ext heq
      exact hww ▸ hw₀
    rcases hW₀min _ hsub hWc' hWi' with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have hvH : v ∈ cuspidalSubspace ω a b Φ₀ := hle' hv
      have hmem : (⟨v, hvH⟩ : ↥(cuspidalSubspace ω a b Φ₀)) ∈ W'.comap (cuspidalSubspace ω a b Φ₀).subtype := hv
      rw [h, Submodule.mem_bot] at hmem
      rw [Submodule.mem_bot]
      exact congrArg Subtype.val hmem
    · right
      refine le_antisymm hW'le ?_
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      have hmem : w ∈ W'.comap (cuspidalSubspace ω a b Φ₀).subtype := h.symm ▸ hw
      exact hmem

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_stable_translateRight_smoothingOperator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_stable_translateRight_smoothingOperator (solution)
