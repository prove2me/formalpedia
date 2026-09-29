-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a7584dc3-b928-5ec1-a549-0260ea9ef951

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem solution
    (θ₀ θ : ℝ) (hθ : θ < θ₀) (N N₂ N₃ : ℕ) :
    ∃ N' : ℕ, ∀ (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Continuous u →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∃ a : Fin (N₂ + 1) → ℂ, a (Fin.last N₂) = 1 ∧ ∑ m, a m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∃ a : Fin (N₃ + 1) → ℂ, a (Fin.last N₃) = 1 ∧ ∑ m, a m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
        (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀)) →
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by
  classical

  obtain ⟨d, d₂, d', d₂', hsys⟩ :=
    exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le N₂ N₃
  obtain ⟨N', hN'⟩ := exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems θ₀ θ hθ N d d₂ d' d₂'
    (6 * N₂ * N₃ + 1) (6 * N₂ * N₃ + 1)
  refine ⟨N', ?_⟩
  intro ω u hc haut hcen hsa hKf hrel₂ hrel₃ hgr hray K hK

  have hz : WhittakerBlock.IsCentreFinite u := by
    obtain ⟨c₁, hc₁⟩ := exists_casimir1_eq_smul_of_isArchSmooth3 ω u hcen hsa
    refine ⟨⟨1, ![-c₁, 1], by simp, ?_⟩, ?_, ?_⟩
    · have hsum : ∑ m : Fin (1 + 1), (![-c₁, 1] : Fin (1 + 1) → ℂ) m • (WhittakerBlock.casimir1^[(m : ℕ)] u) =
          -c₁ • u + WhittakerBlock.casimir1 u := by
        rw [Fin.sum_univ_two]; simp
      rw [hsum, hc₁, neg_smul, neg_add_cancel]
    · obtain ⟨a, ha, h⟩ := hrel₂; exact ⟨N₂, a, ha, h⟩
    · obtain ⟨a, ha, h⟩ := hrel₃; exact ⟨N₃, a, ha, h⟩
  have hmg : IsModerateGrowth3 ℚ u := by
    obtain ⟨C, hC⟩ := hgr []
    exact ⟨C, N, fun g _ => by simpa using hC g⟩
  have hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w) := by
    have h := (continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite u hc hmg hsa hKf
      1 (fun _ => 1) (fun _ => 1) (fun _ => map_one _) ?_).1
    · have hu : (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℂ)) i * u (x * (fun _ : Fin 1 => (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) i)) = u := by
        funext x; simp
      simpa [hu] using h
    · have hu : (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℂ)) i * u (x * (fun _ : Fin 1 => (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) i)) = u := by
        funext x; simp
      simpa [hu] using hz

  obtain ⟨a₂, ha₂, hrel₂⟩ := hrel₂
  obtain ⟨a₃, ha₃, hrel₃⟩ := hrel₃
  obtain ⟨ι, ι', q, q', hq, hq', hdq, hdq', hrt, hrt', hsysu⟩ := hsys ω a₂ ha₂ a₃ ha₃
  have hS := hsysu u hcw haut hcen hsa hKf hrel₂ hrel₃

  have hapr : ∀ w : List (Fin 3 × Fin 3),
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N := by
    intro w
    have hcw' : ∀ w' : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
        (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w) w') := by
      intro w'; rw [← List.foldr_append]; exact hcw (w' ++ w)
    have hgr' : ∀ w' : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w) w' g‖ ≤ C * gauge3 ℚ g ^ N := by
      intro w'; rw [← List.foldr_append]; exact hgr (w' ++ w)
    exact norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact N _ hcw' hgr'

  have h72 := hN' ι ι' q q' ⟨hq, hq', hdq, hdq', hrt, hrt'⟩ u
  have h72a := h72 hS
  have h72b := h72a hapr
  have horth := h72b hray
  exact forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3 θ N' ω u hc haut hcen horth K hK

end S_LanglandsTunnell_CubicInduction_norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder (solution)
