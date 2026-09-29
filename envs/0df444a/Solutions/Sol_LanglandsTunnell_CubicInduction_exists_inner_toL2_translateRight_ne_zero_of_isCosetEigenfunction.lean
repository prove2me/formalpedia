-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/340b6bba-57d1-5e32-97f0-c0c17d69343c

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_stable_translateRight_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_of_irreducible_cuspidal
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open scoped InnerProductSpace

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL localMaximalCompact3 heckeGen1 heckeGen2 IsCosetEigenfunction IsRightInvariant localToAdelic3 WhittakerBlock.IsCentreFinite SlabL2.exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero SlabL2.exists_casimir_eq_smul_of_irreducible_cuspidal exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_monic_rel_of_eq_smul {X : Type*}
    (T : (X → ℂ) → (X → ℂ)) (φ : X → ℂ) (c : ℂ) (h : T φ = c • φ) :
    ∃ (N : ℕ) (a : Fin (N + 1) → ℂ), a (Fin.last N) = 1 ∧ ∑ m, a m • (T^[m] φ) = 0 := by
  refine ⟨1, ![-c, 1], rfl, ?_⟩
  rw [Fin.sum_univ_two]
  show (-c) • (T^[0] φ) + (1 : ℂ) • (T^[1] φ) = 0
  rw [Function.iterate_zero, Function.iterate_one, id, h, one_smul, neg_smul, neg_add_cancel]

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction.LanglandsTunnell.CubicInduction"

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (_hF0 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F (lam2 p))
    (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀) (_hF'0 : toL2 ω a b Φ₀ ⟨F', hF'.1⟩ ≠ 0)
    (_hK' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F')
    (_hT1' : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F' (lam1 p))
    (_hT2' : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F' (lam2 p)) :
    ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ ≠ 0 := by
  classical

  obtain ⟨V₀, hgen₀, hFV₀, htr₀, hsm₀, htrans⟩ :=
    SlabL2.exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero ω _hω a b Φ₀ _hΦ₀ F hF
  have hne₀ : V₀ ≠ ⊥ := by
    intro h
    apply _hF0
    rw [h, Submodule.mem_bot] at hFV₀
    exact hFV₀

  obtain ⟨V, hVle, hgen, hne, htr, hsm, hmin⟩ :=
    SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator ω _hω a b Φ₀ _hΦ₀ V₀ hgen₀ hne₀ htr₀ hsm₀

  have hVF : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V →
      ∀ (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g G ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g G, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 :=
    fun G hG hGV => htrans G hG (hVle hGV)

  obtain ⟨S', hSS', F₁, hF₁, hF₁V, hF₁0, hK₁, hT1₁, hT2₁⟩ :=
    exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero S ω _hω lam1 lam2 a b Φ₀
      _hΦ₀ F hF _hF0 _hK _hT1 _hT2 V hgen hne htr hsm hVF

  obtain ⟨c₁, c₂, c₃, hcas⟩ :=
    SlabL2.exists_casimir_eq_smul_of_irreducible_cuspidal ω _hω a b Φ₀ _hΦ₀ V hgen hne htr hsm hmin
  have hcf : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      smoothingOperator φ F₁ ∈ cuspFunctions ω a b Φ₀ → WhittakerBlock.IsArchSmooth3 (smoothingOperator φ F₁) →
        WhittakerBlock.IsCentreFinite (smoothingOperator φ F₁) := by
    intro φ hφ hφF hsa
    obtain ⟨h1, h2, h3⟩ := hcas (smoothingOperator φ F₁) hφF (hsm F₁ hF₁ hF₁V φ hφ hφF) hsa
    exact ⟨exists_monic_rel_of_eq_smul _ _ _ h1, exists_monic_rel_of_eq_smul _ _ _ h2,
      exists_monic_rel_of_eq_smul _ _ _ h3⟩

  obtain ⟨g, hg, hne1⟩ :=
    exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite S' ω _hω lam1 lam2 a b Φ₀
      _hΦ₀ F₁ hF₁ hF₁0 hK₁ hT1₁ hT2₁ hcf F' hF' _hF'0
      (fun p hp => _hK' p fun h => hp (hSS' h)) (fun p hp => _hT1' p fun h => hp (hSS' h))
      (fun p hp => _hT2' p fun h => hp (hSS' h))

  by_contra hall
  exact hne1 (hVF F₁ hF₁ hF₁V F' hF' (fun g' hg' => by_contra fun h => hall ⟨g', hg', h⟩) g hg)

end S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction (solution)
