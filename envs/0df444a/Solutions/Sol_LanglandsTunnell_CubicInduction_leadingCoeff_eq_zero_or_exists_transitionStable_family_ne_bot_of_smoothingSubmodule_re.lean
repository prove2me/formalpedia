-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1f914e78-e835-522d-af3f-948e6999ea17

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_joint_casimir_eigenvector_apply_ne_zero_of_positive_skew_form
import Theorems.Thm_LanglandsTunnell_CubicInduction_form_casimir_eq_of_skew_archDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_spectralParameter_of_casimir_scalars_and_powerSum_symmetry
import Theorems.Thm_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_upperTriangular_equivariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_neg_half_add_mul_I_of_powerSum_symmetry_of_re_eq_neg_half
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_nontrivial_of_casimir_relations
import Theorems.Thm_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_families_ne_bot_of_inducedPicture_package_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace DichoSkel39953e9d

open LanglandsTunnell.CubicInduction

theorem sum_regroup {m J : ℕ} (e : Fin m → ℂ) (b : Fin m → Fin J → ℂ) (T : Finset (ℂ × ℕ))
    (hT : ∀ i j, (e i, ((j : Fin J) : ℕ)) ∈ T) (f : ℂ × ℕ → ℂ) :
    (∑ t ∈ T, (∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = t then b i j else 0) * f t) =
      ∑ i : Fin m, ∑ j : Fin J, b i j * f (e i, ((j : Fin J) : ℕ)) := by
  classical
  have : ∀ t ∈ T, (∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = t then b i j else 0) * f t =
      ∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = t then b i j * f t else 0 := by
    intro t _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq T (e i, ((j : Fin J) : ℕ)) (fun t => b i j * f t)]
  simp [hT i j]

theorem merge {m J n J' : ℕ} (e : Fin m → ℂ) (e' : Fin n → ℂ)
    (τ ρ' : ℝ) (hρ' : τ ≤ ρ') (W : ℝ → ℂ) (b : Fin m → Fin J → ℂ) (c : Fin n → Fin J' → ℂ)
    (hb : ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖W y - ∑ i : Fin m, ∑ j : Fin J, b i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y ^ τ)
    (hc : ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖W y - ∑ i : Fin n, ∑ j : Fin J', c i j * ((y : ℂ) ^ e' i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y ^ ρ')
    (z : ℂ) (hz : z.re < τ) (q : ℕ) :
    (∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = (z, q) then b i j else 0) =
      ∑ i : Fin n, ∑ j : Fin J', if (e' i, ((j : Fin J') : ℕ)) = (z, q) then c i j else 0 := by
  classical
  let T : Finset (ℂ × ℕ) :=
    (Finset.univ.image fun ij : Fin m × Fin J => (e ij.1, ((ij.2 : Fin J) : ℕ))) ∪
    (Finset.univ.image fun ij : Fin n × Fin J' => (e' ij.1, ((ij.2 : Fin J') : ℕ)))
  have hTb : ∀ i j, (e i, ((j : Fin J) : ℕ)) ∈ T := fun i j =>
    Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hTc : ∀ i j, (e' i, ((j : Fin J') : ℕ)) ∈ T := fun i j =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  by_cases hzq : (z, q) ∈ T
  swap
  · have h1 : ∀ i j, ¬ (e i, ((j : Fin J) : ℕ)) = (z, q) := fun i j h => hzq (h ▸ hTb i j)
    have h2 : ∀ i j, ¬ (e' i, ((j : Fin J') : ℕ)) = (z, q) := fun i j h => hzq (h ▸ hTc i j)
    simp [h1, h2]
  let L : ℂ × ℕ → ℂ := fun t => ∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = t then b i j else 0
  let R : ℂ × ℕ → ℂ := fun t => ∑ i : Fin n, ∑ j : Fin J', if (e' i, ((j : Fin J') : ℕ)) = t then c i j else 0
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨Cc, hCc⟩ := hc
  have key := LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow
    (ι := ↥T) (P := Unit) (fun t => t.1.1) (fun t => t.1.2) (fun t _ => L t.1 - R t.1)
    (by
      intro s t h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2))
    τ
    (fun y _ => (∑ i : Fin m, ∑ j : Fin J, b i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) -
      ∑ i : Fin n, ∑ j : Fin J', c i j * ((y : ℂ) ^ e' i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))
    (fun _ _ => 0)
    (by
      intro _ y _ _
      rw [add_zero, Finset.sum_coe_sort T (fun t => (L t - R t) *
        ((y : ℂ) ^ t.1 * ((Real.log y : ℝ) : ℂ) ^ t.2))]
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [sum_regroup e b T hTb, sum_regroup e' c T hTc])
    (by intro _; exact ⟨0, fun y _ _ => by simp⟩)
    (by
      intro _
      refine ⟨|Cc| + |Cb|, fun y hy hy1 => ?_⟩
      have hyτ : y ^ ρ' ≤ y ^ τ := Real.rpow_le_rpow_of_exponent_ge hy hy1 hρ'
      have hyp : 0 ≤ y ^ τ := Real.rpow_nonneg hy.le τ
      have hyp' : 0 ≤ y ^ ρ' := Real.rpow_nonneg hy.le ρ'
      have e1 := hCb y hy hy1
      have e2 := hCc y hy hy1
      calc ‖(∑ i : Fin m, ∑ j : Fin J, b i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) -
              ∑ i : Fin n, ∑ j : Fin J', c i j * ((y : ℂ) ^ e' i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖
          = ‖(W y - ∑ i : Fin n, ∑ j : Fin J', c i j * ((y : ℂ) ^ e' i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) -
              (W y - ∑ i : Fin m, ∑ j : Fin J, b i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))‖ := by
            congr 1; ring
        _ ≤ Cc * y ^ ρ' + Cb * y ^ τ := (norm_sub_le _ _).trans (add_le_add e2 e1)
        _ ≤ |Cc| * y ^ τ + |Cb| * y ^ τ := by
            have : Cc * y ^ ρ' ≤ |Cc| * y ^ ρ' := mul_le_mul_of_nonneg_right (le_abs_self Cc) hyp'
            have : |Cc| * y ^ ρ' ≤ |Cc| * y ^ τ := mul_le_mul_of_nonneg_left hyτ (abs_nonneg Cc)
            have : Cb * y ^ τ ≤ |Cb| * y ^ τ := mul_le_mul_of_nonneg_right (le_abs_self Cb) hyp
            linarith
        _ = (|Cc| + |Cb|) * y ^ τ := by ring)
    ⟨(z, q), hzq⟩ hz
  have := congr_fun key ()
  simpa [L, R, sub_eq_zero] using this

theorem sum_ite_label {m J : ℕ} (e : Fin m → ℂ) (he : Function.Injective e) (b : Fin m → Fin J → ℂ)
    (i₀ : Fin m) (j₀ : Fin J) (z : ℂ) (q : ℕ) (hz : e i₀ = z) (hq : ((j₀ : Fin J) : ℕ) = q) :
    (∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = (z, q) then b i j else 0) = b i₀ j₀ := by
  classical
  rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _)]
    · simp [hz, hq]
    · intro j _ hj
      have : ((j : Fin J) : ℕ) ≠ q := fun h => hj (Fin.ext (by rw [h, ← hq]))
      simp [this]
  · intro i _ hi
    have : e i ≠ z := fun h => hi (he (h.trans hz.symm))
    simp [this]

theorem sum_ite_label_eq_zero {m J : ℕ} (e : Fin m → ℂ) (b : Fin m → Fin J → ℂ) (z : ℂ) (q : ℕ)
    (h : ∀ i : Fin m, ∀ j : Fin J, e i = z → ((j : Fin J) : ℕ) ≠ q) :
    (∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = (z, q) then b i j else 0) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : e i = z
  · simp [h i j hi]
  · simp [hi]

theorem smul_cancel_of_apply_ne_zero {X : Type*} {F : X → ℂ} {x₀ : X} (hF : F x₀ ≠ 0) {a b : ℂ}
    (h : a • F = b • F) : a = b := by
  have := congr_fun h x₀
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hF this

theorem archDeriv_smul (i j : Fin 3) (z : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.archDeriv i j (z • φ) = z • WhittakerBlock.archDeriv i j φ := by
  funext g
  simp only [WhittakerBlock.archDeriv, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field z

theorem casimir1_smul (z : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir1 (z • φ) = z • WhittakerBlock.casimir1 φ := by
  funext g
  simp only [WhittakerBlock.casimir1, archDeriv_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem casimir1_eq_sum (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir1 φ = ∑ i : Fin 3, WhittakerBlock.archDeriv i i φ := by
  funext g; simp only [WhittakerBlock.casimir1, Finset.sum_apply]

theorem casimir2_eq_sum (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir2 φ =
      ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i φ) := by
  funext g; simp only [WhittakerBlock.casimir2, Finset.sum_apply]

theorem casimir3_eq_sum (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    WhittakerBlock.casimir3 φ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i φ)) := by
  funext g; simp only [WhittakerBlock.casimir3, Finset.sum_apply]

end DichoSkel39953e9d

theorem solution
    (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (hre : ∀ i : Fin m, 1 / 2 ≤ (e i).re)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hJ : 0 < J)
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2)
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (A : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h2 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M ∧
            ∀ (y₂ : ℝ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), A (fun g => w (g * k)) y₂ k' = A w y₂ (k' * k)))
    (h5 :
      (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h6 :
      (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        A (z • w₁ + w₂) y₂ k = z * A w₁ y₂ k + A w₂ y₂ k))
    (h7 :
      (∀ w ∈ M, ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, b i₀ j y₂ k = A w y₂ k) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ))
    (h8 :
      (∀ w ∈ M, ∀ i j : Fin 3, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => A w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))
          (A (WhittakerBlock.archDeriv i j w) y₂ k) 0))
    (h9 :
      (∀ w ∈ M, ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => A w y₂ (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))
          (A (WhittakerBlock.archDeriv c₂ c₁ w) y₂ k - A (WhittakerBlock.archDeriv c₁ c₂ w) y₂ k) 0))
    (h10 :
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (h11 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0))
    (h12 :
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g))
    (h13 :
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N)) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    (∀ w ∈ M, ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, A w y₂ k = 0) ∨
    ∃ σ σ₃ : ℝ,
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I]
    ∃ S S' : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (((∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} ∧
          (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₂ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S (ℓ - 1)) ∧
          (∀ p ∈ S 2, same₂ (Ξ ν₁₂ p) ∈ S 2) ∧
          S 0 = ⊥ ∧
          (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S' ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S' 0 = ⊥ ∧
          S' 1 ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} ∧
          S' 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} ∧
          (∀ ℓ, ∀ p ∈ S' ℓ, lower₂ (Ξ ν₁₂ p) ∈ S' (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S' (ℓ - 1)) ∧
          S' 1 = ⊥) ∨
       ((∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} ∧
          (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₃ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S (ℓ - 1)) ∧
          (∀ p ∈ S 2, same₂ (Ξ ν₁₃ p) ∈ S 2) ∧
          S 0 = ⊥ ∧
          (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S' ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
          S' 0 = ⊥ ∧
          S' 1 ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} ∧
          S' 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} ∧
          (∀ ℓ, ∀ p ∈ S' ℓ, lower₂ (Ξ ν₁₃ p) ∈ S' (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S' (ℓ - 1)) ∧
          S' 1 = ⊥)) ∧
      ((∃ ℓ, S ℓ ≠ ⊥) ∨ (∃ ℓ, S' ℓ ≠ ⊥)) := by
  classical
  by_cases hA : ∀ w ∈ M, ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, A w y₂ k = 0
  · exact Or.inl hA
  · right
    push_neg at hA
    obtain ⟨w₀, hw₀, y₂, hy₂, k, hne⟩ := hA

    obtain ⟨B, hBherm, hBlin, hBpos, hBskew, hBorth⟩ := id h10
    obtain ⟨w, hw, lam₁, lam₂, lam₃, hC1, hC2, hC3, hAw⟩ :=
      exists_joint_casimir_eigenvector_apply_ne_zero_of_positive_skew_form M (fun w hw => (h1 w hw).1) h5
        ⟨B, hBherm, hBlin, hBpos, hBskew, hBorth⟩ h11 A h6 w₀ hw₀ y₂ k hne
    obtain ⟨hsa, hsaW, hcw, haut⟩ := h1 w hw
    obtain ⟨N, hN⟩ := h13 w hw

    obtain ⟨N₁, N₂, N₃, a₁, a₂, a₃, ha₁, ha₂, ha₃, hrel⟩ := id h11
    obtain ⟨ρ₀, hρ₀⟩ :=
      exists_exponents_whittaker3_diag_joint_expansion_nontrivial_of_casimir_relations ω N₂ a₂ ha₂ N₃ a₃ ha₃
    obtain ⟨n, J', e', δ, hδ, he', hre', hexp⟩ := hρ₀ (max τ ρ₀) (le_max_right _ _)
    obtain ⟨⟨c, hcc, hce, c', hc'c, hc'e, hexact⟩, -⟩ :=
      hexp N w hcw haut (h12 w hw) hsa (h3 w hw) (hrel w hw).2.1 (hrel w hw).2.2 hN

    obtain ⟨bcoef, hb_cont, hb_A, hb_exp⟩ := h7 w hw
    have hmerge : ∀ y : ℝ, 0 < y → ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ z : ℂ, z.re < τ → ∀ q : ℕ,
        (∑ i : Fin m, ∑ j : Fin J, if (e i, ((j : Fin J) : ℕ)) = (z, q) then bcoef i j y k' else 0) =
          ∑ i : Fin n, ∑ j : Fin J', if (e' i, ((j : Fin J') : ℕ)) = (z, q) then c i j y k' else 0 := by
      intro y hy k' z hz q
      have hK : IsCompact ({k'} : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) := isCompact_singleton
      have hbd1 : 1 ≤ max y y⁻¹ := by
        rcases le_or_gt 1 y with h | h
        · exact le_max_of_le_left h
        · exact le_max_of_le_right (one_le_inv_iff₀.2 ⟨hy, h.le⟩)
      have hyl : (max y y⁻¹)⁻¹ ≤ y := inv_le_of_inv_le₀ hy (le_max_right _ _)
      have hyu : y ≤ max y y⁻¹ := le_max_left _ _
      obtain ⟨Cb, hCb⟩ := hb_exp {k'} hK (max y y⁻¹) hbd1
      obtain ⟨Cc, hCc⟩ := hce {k'} hK (max y y⁻¹) hbd1
      exact DichoSkel39953e9d.merge e e' τ (max τ ρ₀ + δ) (by have := le_max_left τ ρ₀; linarith)
        (fun y₁ => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ w
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y, y, 1] i else 0) * k'))
        (fun i j => bcoef i j y k') (fun i j => c i j y k')
        ⟨Cb, fun y₁ h1 h2 => hCb k' (Set.mem_singleton k') y hyl hyu y₁ h1 h2⟩
        ⟨Cc, fun y₁ h1 h2 => hCc k' (Set.mem_singleton k') y hyl hyu y₁ h1 h2⟩ z hz q
    have hτ₀ : (e i₀).re < τ := by rw [hD]; exact hτ

    have hcsum : ∀ y : ℝ, 0 < y → ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, A w y k' =
        ∑ i : Fin n, ∑ j : Fin J', if (e' i, ((j : Fin J') : ℕ)) = (e i₀, 0) then c i j y k' else 0 := by
      intro y hy k'
      rw [← hb_A ⟨0, hJ⟩ rfl y hy k', ← hmerge y hy k' (e i₀) hτ₀ 0,
        DichoSkel39953e9d.sum_ite_label e he (fun i j => bcoef i j y k') i₀ ⟨0, hJ⟩ (e i₀) 0 rfl rfl]
    obtain ⟨i9, hi9⟩ : ∃ i' : Fin n, e' i' = e i₀ := by
      by_contra hno
      push_neg at hno
      apply hAw
      rw [hcsum y₂ hy₂ k]
      exact DichoSkel39953e9d.sum_ite_label_eq_zero e' _ _ _ (fun i j hi => absurd hi (hno i))
    have hJ' : 0 < J' := by
      rcases Nat.eq_zero_or_pos J' with h0 | h0
      · exfalso
        apply hAw
        rw [hcsum y₂ hy₂ k]
        subst h0
        simp
      · exact h0
    have hcA : ∀ y : ℝ, 0 < y → ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c i9 ⟨0, hJ'⟩ y k' = A w y k' := by
      intro y hy k'
      rw [hcsum y hy k', DichoSkel39953e9d.sum_ite_label e' he' (fun i j => c i j y k') i9 ⟨0, hJ'⟩ (e i₀) 0 hi9 rfl]
    have hbot₁ : ∀ (i : Fin n) (j : Fin J'), (e' i).re < (e' i9).re →
        ∀ y : ℝ, 0 < y → ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c i j y k' = 0 := by
      intro i j hlt y hy k'
      have hlt' : (e' i).re < 1 / 2 := by rwa [hi9, hD] at hlt
      have h1 := hmerge y hy k' (e' i) (by linarith) ((j : Fin J') : ℕ)
      rw [DichoSkel39953e9d.sum_ite_label e' he' (fun i j => c i j y k') i j (e' i) _ rfl rfl,
        DichoSkel39953e9d.sum_ite_label_eq_zero] at h1
      · exact h1.symm
      · intro i' j' hi' _
        have := hre i'
        rw [hi'] at this
        linarith

    obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j : Fin J' => ∃ y : ℝ, 0 < y ∧ ∃ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c i9 j y k' ≠ 0)
      (fun j => ((j : Fin J') : ℕ))
      ⟨⟨0, hJ'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, y₂, hy₂, k, by rw [hcA y₂ hy₂ k]; exact hAw⟩⟩
    have htop₁ : ∀ j : Fin J', ((j₀ : Fin J') : ℕ) < ((j : Fin J') : ℕ) →
        ∀ y : ℝ, 0 < y → ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c i9 j y k' = 0 := by
      intro j hlt y hy k'
      by_contra hne'
      have := hj₀max j (Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hy, k', hne'⟩)
      omega
    have hnontriv : ∃ (i' : Fin n) (j' : Fin J') (k' : AdelicGL 3 (𝓞 ℚ) ℚ), c' i9 j₀ i' j' k' ≠ 0 := by
      obtain ⟨y, hy, k', hck⟩ := (Finset.mem_filter.1 hj₀mem).2
      by_contra hno
      push_neg at hno
      apply hck
      exact hexact i9 j₀ (fun k'' i'' j'' hlt y' hy' => hbot₁ i'' j'' hlt y' hy' k'')
        (fun k'' i' j' => hno i' j' k'') k' y hy
    obtain ⟨i9', hi9'mem, hi9'min⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i' : Fin n => ∃ (j' : Fin J') (k' : AdelicGL 3 (𝓞 ℚ) ℚ), c' i9 j₀ i' j' k' ≠ 0)
      (fun i' => (e' i').re)
      (by obtain ⟨i', j', k', h⟩ := hnontriv; exact ⟨i', Finset.mem_filter.2 ⟨Finset.mem_univ _, j', k', h⟩⟩)
    have hbot₂ : ∀ (i' : Fin n) (j' : Fin J'), (e' i').re < (e' i9').re →
        ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c' i9 j₀ i' j' k' = 0 := by
      intro i' j' hlt k'
      by_contra hne'
      have := hi9'min i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, j', k', hne'⟩)
      linarith
    obtain ⟨j₀', hj₀'mem, hj₀'max⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j' : Fin J' => ∃ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c' i9 j₀ i9' j' k' ≠ 0)
      (fun j' => ((j' : Fin J') : ℕ))
      (by obtain ⟨j', k', h⟩ := (Finset.mem_filter.1 hi9'mem).2
          exact ⟨j', Finset.mem_filter.2 ⟨Finset.mem_univ _, k', h⟩⟩)
    have htop₂ : ∀ j' : Fin J', ((j₀' : Fin J') : ℕ) < ((j' : Fin J') : ℕ) →
        ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, c' i9 j₀ i9' j' k' = 0 := by
      intro j' hlt k'
      by_contra hne'
      have := hj₀'max j' (Finset.mem_filter.2 ⟨Finset.mem_univ _, k', hne'⟩)
      omega
    obtain ⟨k₀, hFk₀⟩ : ∃ k₀ : AdelicGL 3 (𝓞 ℚ) ℚ, c' i9 j₀ i9' j₀' k₀ ≠ 0 := (Finset.mem_filter.1 hj₀'mem).2

    have hequiv := doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top ω w hcw haut (h12 w hw) hsa
      lam₁ hC1 n J' e' he' (max τ ρ₀ + δ) (fun i => by linarith [hre' i]) c hcc hce c' hc'c hc'e
      i9 i9' j₀ j₀' hbot₁ hbot₂ htop₁ htop₂

    obtain ⟨V, k₁, hV⟩ := exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top M ω h1 h3
      (fun w hw k hk hk' => (h4 w hw k hk hk').1)
      h5 h12 h13 N₂ a₂ ha₂ N₃ a₃ ha₃ (fun w hw => ⟨(hrel w hw).2.1, (hrel w hw).2.2⟩) (max τ ρ₀) n J' e' δ hδ
      he' hre' hexp w hw lam₁ lam₂ lam₃ hC1 hC2 hC3 c hcc hce c' hc'c hc'e i9 i9' j₀ j₀'
      hbot₁ hbot₂ htop₁ htop₂ k₀ hFk₀
    set F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := c' i9 j₀ i9' j₀' with hFdef
    set ν : Fin 3 → ℂ := (![e' i9 - 1, e' i9' - e' i9, lam₁ - e' i9' + 1] : Fin 3 → ℂ) with hνdef
    have hsaF : WhittakerBlock.IsArchSmooth3 F := (hV.2.2.2.2.1 F hV.1).1
    have hCF : WhittakerBlock.casimir1 F = lam₁ • F ∧ WhittakerBlock.casimir2 F = lam₂ • F ∧
        WhittakerBlock.casimir3 F = lam₃ • F := (hV.2.2.2.2.1 F hV.1).2

    obtain ⟨hI1, hI2, hI3⟩ := casimir_eq_smul_of_upperTriangular_equivariant ν F hsaF hequiv
    have hν1 : lam₁ = ∑ a, ν a :=
      DichoSkel39953e9d.smul_cancel_of_apply_ne_zero hFk₀ (hCF.1.symm.trans hI1)
    have hν2 : lam₂ = (∑ a, ν a ^ 2) - 2 :=
      DichoSkel39953e9d.smul_cancel_of_apply_ne_zero hFk₀ (hCF.2.1.symm.trans hI2)
    have hν3 : lam₃ = (∑ a, ν a ^ 3) + (∑ a, ν a ^ 2) - (ν 0 * ν 1 + ν 0 * ν 2 + ν 1 * ν 2) - 2 * (∑ a, ν a) - 3 :=
      DichoSkel39953e9d.smul_cancel_of_apply_ne_zero hFk₀ (hCF.2.2.symm.trans hI3)

    have hw0 : w ≠ 0 := by
      rintro rfl
      apply hAw
      have := h6 1 0 M.zero_mem 0 M.zero_mem y₂ k
      simp only [one_smul, add_zero, one_mul] at this
      linear_combination -this
    have hB0 : ∀ v ∈ M, B 0 v = 0 := by
      intro v hv
      have := hBlin 1 0 M.zero_mem 0 M.zero_mem v hv
      simp only [one_smul, add_zero, one_mul] at this
      linear_combination -this
    have hBsmul : ∀ (z : ℂ), ∀ v ∈ M, ∀ v' ∈ M, B (z • v) v' = z * B v v' := by
      intro z v hv v' hv'
      have := hBlin z v hv 0 M.zero_mem v' hv'
      rwa [add_zero, hB0 v' hv', add_zero] at this
    have hBsmul' : ∀ (z : ℂ), ∀ v ∈ M, ∀ v' ∈ M, B v' (z • v) = (starRingEnd ℂ) z * B v' v := by
      intro z v hv v' hv'
      rw [hBherm (z • v) (M.smul_mem z hv) v' hv', hBsmul z v hv v' hv', map_mul, ← hBherm v hv v' hv']
    set β : ℂ := B w w with hβ
    have hβre : 0 < β.re := hBpos w hw hw0
    have hβ0 : β ≠ 0 := fun h => by rw [h] at hβre; simp at hβre
    obtain ⟨r1, r2, r3⟩ := form_casimir_eq_of_skew_archDeriv M h5 B hBherm hBlin hBskew w hw w hw
    rw [WhittakerBlock.sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2 w hsa] at r3
    rw [hC1, DichoSkel39953e9d.casimir1_smul, hC1, hC2, hC3, smul_smul,
      show lam₃ • w + (lam₁ * lam₁) • w - (3 : ℂ) • lam₂ • w = (lam₃ + lam₁ ^ 2 - 3 * lam₂) • w by
        rw [smul_smul, ← add_smul, ← sub_smul]; ring_nf] at r3
    rw [hC1] at r1
    rw [hC2] at r2
    rw [hBsmul _ w hw w hw, hBsmul' _ w hw w hw] at r1 r2 r3
    have hre1 : lam₁.re = 0 := by
      have : lam₁ = -(starRingEnd ℂ) lam₁ := mul_right_cancel₀ hβ0 (r1.trans (neg_mul _ _).symm)
      have := congrArg Complex.re this
      simp at this
      linarith
    have him2 : lam₂.im = 0 := by
      have : lam₂ = (starRingEnd ℂ) lam₂ := mul_right_cancel₀ hβ0 r2
      have := congrArg Complex.im this
      simp at this
      linarith
    have hcub : lam₃ + (starRingEnd ℂ) (lam₃ + lam₁ ^ 2 - 3 * lam₂) = 0 := by
      have : lam₃ = -(starRingEnd ℂ) (lam₃ + lam₁ ^ 2 - 3 * lam₂) :=
        mul_right_cancel₀ hβ0 (r3.trans (neg_mul _ _).symm)
      linear_combination this

    obtain ⟨hp1, hp2, hp3⟩ :=
      (exists_spectralParameter_of_casimir_scalars_and_powerSum_symmetry lam₁ lam₂ lam₃).2 ν hν1 hν2 hν3
        hre1 him2 hcub

    have hν0 : (ν 0).re = -1 / 2 := by
      simp only [hνdef, Matrix.cons_val_zero, Complex.sub_re, Complex.one_re, hi9, hD]; norm_num
    obtain ⟨σ, σ₃, b, cix, hb0, hc0, hbc, hνa, hνb, hνc⟩ :=
      exists_eq_neg_half_add_mul_I_of_powerSum_symmetry_of_re_eq_neg_half ν hp1 hp2 hp3 0 hν0
    refine ⟨σ, σ₃, ?_⟩

    have hpos : (b = 1 ∧ cix = 2) ∨ (b = 2 ∧ cix = 1) := by
      have key : ∀ b' c' : Fin 3, b' ≠ 0 → c' ≠ 0 → b' ≠ c' → (b' = 1 ∧ c' = 2) ∨ (b' = 2 ∧ c' = 1) := by
        decide
      exact key b cix hb0 hc0 hbc
    rcases hpos with ⟨hb1, hc2⟩ | ⟨hb2, hc1⟩
    ·
      rw [hb1] at hνb
      rw [hc2] at hνc
      have hν12 : ν = (![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] : Fin 3 → ℂ) := by
        funext a; fin_cases a <;> simp [hνa, hνb, hνc]
      rw [hν12] at hV

      obtain ⟨S, S', hblk, hnt⟩ :=
        exists_transitionStable_families_ne_bot_of_inducedPicture_package_top M ω h1 h3
          (fun w hw k hk hk' => (h4 w hw k hk hk').1) h5 h10 h11 h12 h13 N₂ a₂ ha₂ N₃ a₃ ha₃
          (fun w hw => ⟨(hrel w hw).2.1, (hrel w hw).2.2⟩) (max τ ρ₀) n J' e' δ hδ he' hre' hexp
          i9 i9' j₀ j₀' lam₁ lam₂ lam₃ σ σ₃ 1 2 (by decide) (by decide) (by decide)
          (![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] : Fin 3 → ℂ) (by simp) (by simp) (by simp) (hν12.symm.trans hνdef) F V k₁ hV
      exact ⟨S, S', Or.inl hblk, hnt⟩
    ·
      rw [hb2] at hνb
      rw [hc1] at hνc
      have hν13 : ν = (![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] : Fin 3 → ℂ) := by
        funext a; fin_cases a <;> simp [hνa, hνb, hνc]
      rw [hν13] at hV
      obtain ⟨S, S', hblk, hnt⟩ :=
        exists_transitionStable_families_ne_bot_of_inducedPicture_package_top M ω h1 h3
          (fun w hw k hk hk' => (h4 w hw k hk hk').1) h5 h10 h11 h12 h13 N₂ a₂ ha₂ N₃ a₃ ha₃
          (fun w hw => ⟨(hrel w hw).2.1, (hrel w hw).2.2⟩) (max τ ρ₀) n J' e' δ hδ he' hre' hexp
          i9 i9' j₀ j₀' lam₁ lam₂ lam₃ σ σ₃ 2 1 (by decide) (by decide) (by decide)
          (![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] : Fin 3 → ℂ) (by simp) (by simp) (by simp) (hν13.symm.trans hνdef) F V k₁ hV
      exact ⟨S, S', Or.inr hblk, hnt⟩

end S_LanglandsTunnell_CubicInduction_leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re (solution)
