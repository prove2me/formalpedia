-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/87153e05-2250-50dc-b27e-0b994600adc2

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm
import Theorems.Thm_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero
import Theorems.Thm_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_sum_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_archRealLift3_mul_of_archComponent3_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock

namespace AsmAux

local notation "GG" => AdelicGL 3 (𝓞 ℚ) ℚ

section Calculus

theorem D_smooth {φ : GG → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (archDeriv i j φ) :=
  isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.1 φ hφ i j

theorem D_add {φ ψ : GG → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) (hψ : WhittakerBlock.IsArchSmooth3 ψ)
    (i j : Fin 3) : archDeriv i j (φ + ψ) = archDeriv i j φ + archDeriv i j ψ :=
  isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.1 φ ψ hφ hψ i j

theorem D_smul (c : ℂ) (φ : GG → ℂ) (i j : Fin 3) : archDeriv i j (c • φ) = c • archDeriv i j φ :=
  isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.2.1 c φ i j

theorem casimir1_eq (φ : GG → ℂ) : casimir1 φ = ∑ i : Fin 3, archDeriv i i φ := by
  funext g; simp only [casimir1, Finset.sum_apply]

theorem casimir2_eq (φ : GG → ℂ) : casimir2 φ = ∑ i : Fin 3, ∑ j : Fin 3, archDeriv i j (archDeriv j i φ) := by
  funext g; simp only [casimir2, Finset.sum_apply]

theorem casimir3_eq (φ : GG → ℂ) :
    casimir3 φ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv j k (archDeriv k i φ)) := by
  funext g; simp only [casimir3, Finset.sum_apply]

theorem rev_eq (φ : GG → ℂ) :
    (fun g : GG => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv k i (archDeriv j k φ)) g) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv k i (archDeriv j k (archDeriv i j φ)) := by
  funext g
  simp only [Finset.sum_apply]

  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end Calculus

section Module

variable (M : Submodule ℂ (GG → ℂ))

theorem casimir1_mem (h5 : ∀ w ∈ M, ∀ i j : Fin 3, archDeriv i j w ∈ M) {w : GG → ℂ} (hw : w ∈ M) : casimir1 w ∈ M := by
  rw [casimir1_eq]; exact Submodule.sum_mem _ fun i _ => h5 w hw i i

theorem casimir2_mem (h5 : ∀ w ∈ M, ∀ i j : Fin 3, archDeriv i j w ∈ M) {w : GG → ℂ} (hw : w ∈ M) : casimir2 w ∈ M := by
  rw [casimir2_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => h5 _ (h5 w hw j i) i j

theorem casimir3_mem (h5 : ∀ w ∈ M, ∀ i j : Fin 3, archDeriv i j w ∈ M) {w : GG → ℂ} (hw : w ∈ M) : casimir3 w ∈ M := by
  rw [casimir3_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ =>
    h5 _ (h5 _ (h5 w hw k i) j k) i j

theorem casimir1_add (h1 : ∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w)
    (_h5 : ∀ w ∈ M, ∀ i j : Fin 3, archDeriv i j w ∈ M) {w₁ w₂ : GG → ℂ} (hw₁ : w₁ ∈ M) (hw₂ : w₂ ∈ M) :
    casimir1 (w₁ + w₂) = casimir1 w₁ + casimir1 w₂ := by
  rw [casimir1_eq, casimir1_eq, casimir1_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => D_add (h1 _ hw₁) (h1 _ hw₂) i i

theorem casimir2_add (h1 : ∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, archDeriv i j w ∈ M) {w₁ w₂ : GG → ℂ} (hw₁ : w₁ ∈ M) (hw₂ : w₂ ∈ M) :
    casimir2 (w₁ + w₂) = casimir2 w₁ + casimir2 w₂ := by
  rw [casimir2_eq, casimir2_eq, casimir2_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D_add (h1 _ hw₁) (h1 _ hw₂), D_add (h1 _ (h5 _ hw₁ j i)) (h1 _ (h5 _ hw₂ j i))]

theorem casimir3_add (h1 : ∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, archDeriv i j w ∈ M) {w₁ w₂ : GG → ℂ} (hw₁ : w₁ ∈ M) (hw₂ : w₂ ∈ M) :
    casimir3 (w₁ + w₂) = casimir3 w₁ + casimir3 w₂ := by
  rw [casimir3_eq, casimir3_eq, casimir3_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [D_add (h1 _ hw₁) (h1 _ hw₂), D_add (h1 _ (h5 _ hw₁ k i)) (h1 _ (h5 _ hw₂ k i)),
    D_add (h1 _ (h5 _ (h5 _ hw₁ k i) j k)) (h1 _ (h5 _ (h5 _ hw₂ k i) j k))]

theorem casimir1_smul (c : ℂ) (w : GG → ℂ) : casimir1 (c • w) = c • casimir1 w := by
  rw [casimir1_eq, casimir1_eq, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => D_smul c w i i

theorem casimir2_smul (c : ℂ) (w : GG → ℂ) : casimir2 (c • w) = c • casimir2 w := by
  rw [casimir2_eq, casimir2_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D_smul, D_smul]

theorem casimir3_smul (c : ℂ) (w : GG → ℂ) : casimir3 (c • w) = c • casimir3 w := by
  rw [casimir3_eq, casimir3_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [D_smul, D_smul, D_smul]

end Module

end AsmAux

namespace AsmAux

def Blk (ρ δ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))

def Equi (ν : Fin 3 → ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
      (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g

theorem Equi.add {ν : Fin 3 → ℂ} {G₁ G₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (h₁ : Equi ν G₁) (h₂ : Equi ν G₂) :
    Equi ν (G₁ + G₂) := fun t ht hp g => by
  simp only [Pi.add_apply, h₁ t ht hp g, h₂ t ht hp g]; ring

theorem Equi.smul {ν : Fin 3 → ℂ} {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (c : ℂ) (h : Equi ν G) :
    Equi ν (c • G) := fun t ht hp g => by
  simp only [Pi.smul_apply, smul_eq_mul, h t ht hp g]; ring

theorem Equi.zero (ν : Fin 3 → ℂ) : Equi ν (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := fun t ht hp g => by simp

theorem Equi.translate {ν : Fin 3 → ℂ} {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (h : Equi ν G) (k' : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Equi ν (fun g => G (g * k')) := fun t ht hp g => by
  show G (WhittakerBlock.archRealLift3 t * g * k') = _
  rw [mul_assoc]; exact h t ht hp (g * k')

theorem Equi.of_hasDerivAt {ν : Fin 3 → ℂ} {G G' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (h : Equi ν G)
    (γ : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ) (hd : ∀ g, HasDerivAt (fun s : ℝ => G (g * γ s)) (G' g) 0) : Equi ν G' := by
  intro t ht hp g
  have h1 := hd (WhittakerBlock.archRealLift3 t * g)
  have h2 : HasDerivAt (fun s : ℝ => G (WhittakerBlock.archRealLift3 t * g * γ s))
      ((∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G' g) 0 := by
    have := (hd g).const_mul (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [mul_assoc]
    exact h t ht hp (g * γ s)
  exact h1.unique h2

theorem whittaker3_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ (fun _ => (0 : ℂ)) g = 0 := by
  simp [whittaker3]

theorem continuous_sum_fn {ι : Type*} (s : Finset ι) (F : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h : ∀ i ∈ s, Continuous (F i)) : Continuous (∑ i ∈ s, F i) := by
  have : (∑ i ∈ s, F i) = fun a => ∑ i ∈ s, F i a := by funext a; exact Finset.sum_apply _ _ _
  rw [this]; exact continuous_finsetSum s h

end AsmAux

open AsmAux in
theorem solution
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (h5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h12 :
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g))
    (h13 :
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N))
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (hrel : ∀ w ∈ M,
      (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧ (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ) (he : Function.Injective e)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hexp : ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0)))
    (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw : w ∈ M) (lam₁ lam₂ lam₃ : ℂ)
    (hC1 : WhittakerBlock.casimir1 w = lam₁ • w) (hC2 : WhittakerBlock.casimir2 w = lam₂ • w)
    (hC3 : WhittakerBlock.casimir3 w = lam₃ • w)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcc : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (hce : (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)))
    (c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc'c : ∀ i j i' j', Continuous (c' i j i' j'))
    (hc'e : (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖c i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, c' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (i9 i9' : Fin n) (j₀ j₀' : Fin J)
    (hbot₁ : ∀ (i : Fin n) (j : Fin J), (e i).re < (e i9).re → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, c i j y₂ k = 0)
    (hbot₂ : ∀ (i' : Fin n) (j' : Fin J), (e i').re < (e i9').re → ∀ k, c' i9 j₀ i' j' k = 0)
    (htop₁ : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, c i9 j y₂ k = 0)
    (htop₂ : ∀ j' : Fin J, (j₀' : ℕ) < (j' : ℕ) → ∀ k, c' i9 j₀ i9' j' k = 0)
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₀ : c' i9 j₀ i9' j₀' k₀ ≠ 0) :
    ∃ (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ),
      (c' i9 j₀ i9' j₀' ∈ V ∧
      archComponent3 (𝓞 ℚ) ℚ k₁ = 1 ∧
      (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧
        c' i9 j₀ i9' j₀' (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) ∧
      (∀ G ∈ V, Continuous G) ∧
      (∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ V, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ ((![e i9 - 1, e i9' - e i9, lam₁ - e i9' + 1] : Fin 3 → ℂ) a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ V, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ V) ∧
      (∀ G ∈ V, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ V, ∃ v ∈ M, ∃ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
          (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)) ∧
        G = cv' i9 j₀ i9' j₀'))  := by
  classical

  let ν : Fin 3 → ℂ := ![e i9 - 1, e i9' - e i9, lam₁ - e i9' + 1]
  let Eig : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop := fun v =>
    WhittakerBlock.casimir1 v = lam₁ • v ∧ WhittakerBlock.casimir2 v = lam₂ • v ∧ WhittakerBlock.casimir3 v = lam₃ • v
  let Good : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → Prop := fun G =>
    ∃ v ∈ M, Eig v ∧ ∃ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Blk ρ δ n J e v cv cv' ∧ G = cv' i9 j₀ i9' j₀' ∧ Equi ν G

  have hMblk : ∀ u ∈ M, ∃ (cu : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cu' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Blk ρ δ n J e u cu cu' := by
    intro u hu
    obtain ⟨N, hN⟩ := h13 u hu
    obtain ⟨⟨c, hcc, hce, c', hc'c, hc'e, -⟩, -⟩ := hexp N u (h1 u hu).2.2.1 (h1 u hu).2.2.2 (h12 u hu) (h1 u hu).1
      (h3 u hu) (hrel u hu).1 (hrel u hu).2 hN
    exact ⟨c, c', hcc, hce, hc'c, hc'e⟩

  have hsum : ∀ (m : ℕ) (v : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : ∀ l, Continuous (v l))
      (cv : Fin m → Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin m → Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (hb : ∀ l, Blk ρ δ n J e (v l) (cv l) (cv' l)) (a : Fin m → ℂ),
      Blk ρ δ n J e (fun g => ∑ l : Fin m, a l * v l g) (fun i j y k => ∑ l : Fin m, a l * cv l i j y k)
        (fun i j i' j' k => ∑ l : Fin m, a l * cv' l i j i' j' k) :=
    fun m v hv cv cv' hb a => joint_expansion_sum_mul ρ n J e δ m v hv cv cv' hb a

  have htr : ∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Blk ρ δ n J e v cv cv' →
      ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, Blk ρ δ n J e (fun g => v (g * k')) (fun i j y k => cv i j y (k * k'))
        (fun i j i' j' k => cv' i j i' j' (k * k')) :=
    fun v cv cv' hb k' => joint_expansion_comp_mul_right ρ n J e δ v cv cv' hb k'

  have hMcont : ∀ u ∈ M, Continuous u := fun u hu => by
    have := (h1 u hu).2.2.1 []
    simpa using this

  have huniq : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous u →
      ∀ (cu du : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cu' du' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Blk ρ δ n J e u cu cu' → Blk ρ δ n J e u du du' → cu' = du' := by
    intro u hu cu du cu' du' hc hd

    have hb := hsum 2 ![u, u] (fun l => by fin_cases l <;> simpa using hu) ![cu, du] ![cu', du']
      (fun l => by fin_cases l <;> [simpa using hc; simpa using hd]) ![1, -1]
    have hzero : (fun g => ∑ l : Fin 2, (![1, -1] : Fin 2 → ℂ) l * (![u, u] : Fin 2 → _) l g) = fun _ => (0 : ℂ) := by
      funext g; simp [Fin.sum_univ_two]
    rw [hzero] at hb
    funext i j i' j' k
    have hW : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (fun _ => (0 : ℂ))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) = 0 :=
      fun y₁ y₂ _ _ => whittaker3_zero _
    have := (joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero (fun _ => (0 : ℂ)) ρ n J e δ hδ he hre
      (fun i j y k => ∑ l : Fin 2, (![1, -1] : Fin 2 → ℂ) l * (![cu, du] : Fin 2 → _) l i j y k)
      (fun i j i' j' k => ∑ l : Fin 2, (![1, -1] : Fin 2 → ℂ) l * (![cu', du'] : Fin 2 → _) l i j i' j' k) hb k hW).2
      i j i' j'
    simp [Fin.sum_univ_two] at this
    linear_combination this

  let V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    { carrier := {G | Good G}
      zero_mem' := by
        refine ⟨0, M.zero_mem, ?_, fun _ _ _ _ => 0, fun _ _ _ _ _ => 0, ?_, ?_, Equi.zero ν⟩
        · refine ⟨?_, ?_, ?_⟩
          · simpa using AsmAux.casimir1_smul (0 : ℂ) (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
          · simpa using AsmAux.casimir2_smul (0 : ℂ) (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
          · simpa using AsmAux.casimir3_smul (0 : ℂ) (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        · have hb := hsum 0 (fun _ => 0) (fun _ => continuous_const) (fun _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0)
            (fun l => Fin.elim0 l) (fun _ => 0)
          simp at hb
          exact hb
        · rfl
      add_mem' := by
        rintro G₁ G₂ ⟨v₁, hv₁, he₁, cv₁, cv₁', hb₁, rfl, hq₁⟩ ⟨v₂, hv₂, he₂, cv₂, cv₂', hb₂, rfl, hq₂⟩
        refine ⟨v₁ + v₂, M.add_mem hv₁ hv₂, ?_, fun i j y k => cv₁ i j y k + cv₂ i j y k,
          fun i j i' j' k => cv₁' i j i' j' k + cv₂' i j i' j' k, ?_, rfl, hq₁.add hq₂⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [AsmAux.casimir1_add M (fun w hw => (h1 w hw).1) h5 hv₁ hv₂, he₁.1, he₂.1, smul_add]
          · rw [AsmAux.casimir2_add M (fun w hw => (h1 w hw).1) h5 hv₁ hv₂, he₁.2.1, he₂.2.1, smul_add]
          · rw [AsmAux.casimir3_add M (fun w hw => (h1 w hw).1) h5 hv₁ hv₂, he₁.2.2, he₂.2.2, smul_add]
        · have hb := hsum 2 ![v₁, v₂] (fun l => by fin_cases l <;> [simpa using hMcont v₁ hv₁; simpa using hMcont v₂ hv₂])
            ![cv₁, cv₂] ![cv₁', cv₂'] (fun l => by fin_cases l <;> [simpa using hb₁; simpa using hb₂]) ![1, 1]
          have e1 : (fun g => ∑ l : Fin 2, (![1, 1] : Fin 2 → ℂ) l * (![v₁, v₂] : Fin 2 → _) l g) = v₁ + v₂ := by
            funext g; simp [Fin.sum_univ_two]
          have e2 : (fun i j y k => ∑ l : Fin 2, (![1, 1] : Fin 2 → ℂ) l * (![cv₁, cv₂] : Fin 2 → _) l i j y k) =
              fun i j y k => cv₁ i j y k + cv₂ i j y k := by
            funext i j y k; simp [Fin.sum_univ_two]
          have e3 : (fun i j i' j' k => ∑ l : Fin 2, (![1, 1] : Fin 2 → ℂ) l * (![cv₁', cv₂'] : Fin 2 → _) l i j i' j' k) =
              fun i j i' j' k => cv₁' i j i' j' k + cv₂' i j i' j' k := by
            funext i j i' j' k; simp [Fin.sum_univ_two]
          rw [e1, e2, e3] at hb
          exact hb
      smul_mem' := by
        rintro a G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩
        refine ⟨a • v, M.smul_mem a hv, ?_, fun i j y k => a * cv i j y k, fun i j i' j' k => a * cv' i j i' j' k, ?_,
          rfl, hq.smul a⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [AsmAux.casimir1_smul, hev.1, smul_comm]
          · rw [AsmAux.casimir2_smul, hev.2.1, smul_comm]
          · rw [AsmAux.casimir3_smul, hev.2.2, smul_comm]
        · have hb' := hsum 1 ![v] (fun l => by fin_cases l; simpa using hMcont v hv) ![cv] ![cv']
            (fun l => by fin_cases l; simpa using hb) ![a]
          have e1 : (fun g => ∑ l : Fin 1, (![a] : Fin 1 → ℂ) l * (![v] : Fin 1 → _) l g) = a • v := by
            funext g; simp
          have e2 : (fun i j y k => ∑ l : Fin 1, (![a] : Fin 1 → ℂ) l * (![cv] : Fin 1 → _) l i j y k) =
              fun i j y k => a * cv i j y k := by
            funext i j y k; simp
          have e3 : (fun i j i' j' k => ∑ l : Fin 1, (![a] : Fin 1 → ℂ) l * (![cv'] : Fin 1 → _) l i j i' j' k) =
              fun i j i' j' k => a * cv' i j i' j' k := by
            funext i j i' j' k; simp
          rw [e1, e2, e3] at hb'
          exact hb' }
  have hVmem : ∀ G, G ∈ V ↔ Good G := fun G => Iff.rfl

  have hDdata : ∀ v ∈ M, ∀ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Blk ρ δ n J e v cv cv' → ∀ c₀ d₀ : Fin 3,
      ∃ (dv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (dv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        Blk ρ δ n J e (archDeriv c₀ d₀ v) dv dv' ∧
        (∀ g, HasDerivAt (fun s : ℝ => cv' i9 j₀ i9' j₀' (g * WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)))
          (dv' i9 j₀ i9' j₀' g) 0) ∧
        archDeriv c₀ d₀ (cv' i9 j₀ i9' j₀') = dv' i9 j₀ i9' j₀' := by
    intro v hv cv cv' hb c₀ d₀
    obtain ⟨dv, dv', hdb⟩ := hMblk _ (h5 v hv c₀ d₀)
    have hflow := hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv v (h1 v hv) c₀ d₀ ρ n J e δ hδ he hre
      cv cv' hb dv dv' hdb
    refine ⟨dv, dv', hdb, fun g => hflow i9 j₀ i9' j₀' g, ?_⟩
    funext g
    exact (hflow i9 j₀ i9' j₀' g).deriv

  have hsmulBlk : ∀ (a : ℂ) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous v →
      ∀ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Blk ρ δ n J e v cv cv' → Blk ρ δ n J e (a • v) (fun i j y k => a * cv i j y k) (fun i j i' j' k => a * cv' i j i' j' k) := by
    intro a v hvc cv cv' hb
    have hb' := hsum 1 ![v] (fun l => by fin_cases l; simpa using hvc) ![cv] ![cv'] (fun l => by fin_cases l; simpa using hb) ![a]
    have e1 : (fun g => ∑ l : Fin 1, (![a] : Fin 1 → ℂ) l * (![v] : Fin 1 → _) l g) = a • v := by funext g; simp
    have e2 : (fun i j y k => ∑ l : Fin 1, (![a] : Fin 1 → ℂ) l * (![cv] : Fin 1 → _) l i j y k) =
        fun i j y k => a * cv i j y k := by funext i j y k; simp
    have e3 : (fun i j i' j' k => ∑ l : Fin 1, (![a] : Fin 1 → ℂ) l * (![cv'] : Fin 1 → _) l i j i' j' k) =
        fun i j i' j' k => a * cv' i j i' j' k := by funext i j i' j' k; simp
    rw [e1, e2, e3] at hb'; exact hb'
  have hsum3 : ∀ (v : Fin 3 → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), (∀ l, Continuous (v l)) →
      ∀ (cv : Fin 3 → Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin 3 → Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), (∀ l, Blk ρ δ n J e (v l) (cv l) (cv' l)) →
      Blk ρ δ n J e (∑ l, v l) (fun i j y k => ∑ l, cv l i j y k) (fun i j i' j' k => ∑ l, cv' l i j i' j' k) := by
    intro v hvc cv cv' hb
    have hb' := hsum 3 v hvc cv cv' hb (fun _ => 1)
    have e1 : (fun g => ∑ l : Fin 3, (1 : ℂ) * v l g) = ∑ l, v l := by funext g; simp [Finset.sum_apply]
    have e2 : (fun i j y k => ∑ l : Fin 3, (1 : ℂ) * cv l i j y k) = fun i j y k => ∑ l, cv l i j y k := by
      funext i j y k; simp
    have e3 : (fun i j i' j' k => ∑ l : Fin 3, (1 : ℂ) * cv' l i j i' j' k) = fun i j i' j' k => ∑ l, cv' l i j i' j' k := by
      funext i j i' j' k; simp
    rw [e1, e2, e3] at hb'; exact hb'
  have hEigCoeff : ∀ v ∈ M, Eig v → ∀ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Blk ρ δ n J e v cv cv' →
      WhittakerBlock.casimir1 (cv' i9 j₀ i9' j₀') = lam₁ • cv' i9 j₀ i9' j₀' ∧
      WhittakerBlock.casimir2 (cv' i9 j₀ i9' j₀') = lam₂ • cv' i9 j₀ i9' j₀' ∧
      WhittakerBlock.casimir3 (cv' i9 j₀ i9' j₀') = lam₃ • cv' i9 j₀ i9' j₀' := by
    intro v hv hev cv cv' hb

    choose dv dv' hD using fun (p : Fin 3 × Fin 3) => hDdata v hv cv cv' hb p.1 p.2
    have hdmem : ∀ p : Fin 3 × Fin 3, archDeriv p.1 p.2 v ∈ M := fun p => h5 v hv p.1 p.2

    choose ddv ddv' hDD using fun (q : (Fin 3 × Fin 3) × (Fin 3 × Fin 3)) =>
      hDdata _ (hdmem q.2) (dv q.2) (dv' q.2) (hD q.2).1 q.1.1 q.1.2
    have hddmem : ∀ q : (Fin 3 × Fin 3) × (Fin 3 × Fin 3), archDeriv q.1.1 q.1.2 (archDeriv q.2.1 q.2.2 v) ∈ M :=
      fun q => h5 _ (hdmem q.2) q.1.1 q.1.2

    choose dddv dddv' hDDD using fun (r : (Fin 3 × Fin 3) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))) =>
      hDdata _ (hddmem r.2) (ddv r.2) (ddv' r.2) (hDD r.2).1 r.1.1 r.1.2

    have hbl : ∀ lam : ℂ, Blk ρ δ n J e (lam • v) (fun i j y k => lam * cv i j y k) (fun i j i' j' k => lam * cv' i j i' j' k) :=
      fun lam => hsmulBlk lam v (hMcont v hv) cv cv' hb
    refine ⟨?_, ?_, ?_⟩
    ·
      have hb1 := hsum3 (fun l => archDeriv l l v) (fun l => hMcont _ (hdmem (l, l))) (fun l => dv (l, l)) (fun l => dv' (l, l))
        (fun l => (hD (l, l)).1)
      have e1 : (∑ l, archDeriv l l v) = lam₁ • v := by rw [← AsmAux.casimir1_eq]; exact hev.1
      rw [e1] at hb1
      have hu := huniq (lam₁ • v) ((hMcont v hv).const_smul lam₁) _ _ _ _ hb1 (hbl lam₁)
      rw [AsmAux.casimir1_eq]
      funext g
      have := congrFun (congrFun (congrFun (congrFun (congrFun hu i9) j₀) i9') j₀') g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => by rw [(hD (l, l)).2.2]
    ·
      have hb2 : Blk ρ δ n J e (∑ i, ∑ j, archDeriv i j (archDeriv j i v))
          (fun a b y k => ∑ i, ∑ j, ddv ((i, j), (j, i)) a b y k)
          (fun a b a' b' k => ∑ i, ∑ j, ddv' ((i, j), (j, i)) a b a' b' k) := by
        refine hsum3 (fun i => ∑ j, archDeriv i j (archDeriv j i v)) (fun i => ?_) (fun i a b y k => ∑ j, ddv ((i, j), (j, i)) a b y k)
          (fun i a b a' b' k => ∑ j, ddv' ((i, j), (j, i)) a b a' b' k) (fun i => ?_)
        · exact AsmAux.continuous_sum_fn _ _ fun j _ => hMcont _ (hddmem ((i, j), (j, i)))
        · exact hsum3 (fun j => archDeriv i j (archDeriv j i v)) (fun j => hMcont _ (hddmem ((i, j), (j, i))))
            (fun j => ddv ((i, j), (j, i))) (fun j => ddv' ((i, j), (j, i))) (fun j => (hDD ((i, j), (j, i))).1)
      have e2 : (∑ i, ∑ j, archDeriv i j (archDeriv j i v)) = lam₂ • v := by rw [← AsmAux.casimir2_eq]; exact hev.2.1
      rw [e2] at hb2
      have hu := huniq (lam₂ • v) ((hMcont v hv).const_smul lam₂) _ _ _ _ hb2 (hbl lam₂)
      rw [AsmAux.casimir2_eq]
      funext g
      have := congrFun (congrFun (congrFun (congrFun (congrFun hu i9) j₀) i9') j₀') g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [(hD (j, i)).2.2, (hDD ((i, j), (j, i))).2.2]
    ·
      have hb3 : Blk ρ δ n J e (∑ i, ∑ j, ∑ l, archDeriv i j (archDeriv j l (archDeriv l i v)))
          (fun a b y k => ∑ i, ∑ j, ∑ l, dddv ((i, j), ((j, l), (l, i))) a b y k)
          (fun a b a' b' k => ∑ i, ∑ j, ∑ l, dddv' ((i, j), ((j, l), (l, i))) a b a' b' k) := by
        refine hsum3 _ (fun i => ?_) (fun i a b y k => ∑ j, ∑ l, dddv ((i, j), ((j, l), (l, i))) a b y k)
          (fun i a b a' b' k => ∑ j, ∑ l, dddv' ((i, j), ((j, l), (l, i))) a b a' b' k) (fun i => ?_)
        · exact AsmAux.continuous_sum_fn _ _ fun j _ => AsmAux.continuous_sum_fn _ _ fun l _ => hMcont _ (h5 _ (hddmem ((j, l), (l, i))) i j)
        · refine hsum3 _ (fun j => ?_) (fun j a b y k => ∑ l, dddv ((i, j), ((j, l), (l, i))) a b y k)
            (fun j a b a' b' k => ∑ l, dddv' ((i, j), ((j, l), (l, i))) a b a' b' k) (fun j => ?_)
          · exact AsmAux.continuous_sum_fn _ _ fun l _ => hMcont _ (h5 _ (hddmem ((j, l), (l, i))) i j)
          · exact hsum3 _ (fun l => hMcont _ (h5 _ (hddmem ((j, l), (l, i))) i j)) (fun l => dddv ((i, j), ((j, l), (l, i))))
              (fun l => dddv' ((i, j), ((j, l), (l, i)))) (fun l => (hDDD ((i, j), ((j, l), (l, i)))).1)
      have e3 : (∑ i, ∑ j, ∑ l, archDeriv i j (archDeriv j l (archDeriv l i v))) = lam₃ • v := by
        rw [← AsmAux.casimir3_eq]; exact hev.2.2
      rw [e3] at hb3
      have hu := huniq (lam₃ • v) ((hMcont v hv).const_smul lam₃) _ _ _ _ hb3 (hbl lam₃)
      rw [AsmAux.casimir3_eq]
      funext g
      have := congrFun (congrFun (congrFun (congrFun (congrFun hu i9) j₀) i9') j₀') g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [(hD (l, i)).2.2, (hDD ((j, l), (l, i))).2.2, (hDDD ((i, j), ((j, l), (l, i)))).2.2]

  have hFin : ∀ v ∈ M, ∀ (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Blk ρ δ n J e v cv cv' →
      ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => cv' i9 j₀ i9' j₀' (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
    intro v hv cv cv' hb
    obtain ⟨sv, hsv⟩ := h3 v hv

    let T : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := Submodule.span ℂ
      {u | ∃ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) ∧
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 ∧ u = fun g => v (g * k')}
    have hTle : T ≤ Submodule.span ℂ (sv : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
      apply Submodule.span_le.2
      rintro u ⟨k', hk1, hk2, rfl⟩
      exact hsv k' hk1 hk2
    have hTM : T ≤ M := by
      apply Submodule.span_le.2
      rintro u ⟨k', hk1, hk2, rfl⟩
      exact h4 v hv k' hk1 hk2
    haveI : Module.Finite ℂ (Submodule.span ℂ (sv : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :=
      Module.Finite.span_of_finite ℂ sv.finite_toSet
    haveI : Module.Finite ℂ T := Module.Finite.of_injective (Submodule.inclusion hTle) (Submodule.inclusion_injective _)
    let bT := Module.finBasis ℂ T

    have hbmem : ∀ l, (bT l : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ M := fun l => hTM (bT l).2
    choose cb cb' hcb using fun l => hMblk _ (hbmem l)
    refine ⟨Finset.univ.image fun l => cb' l i9 j₀ i9' j₀', fun k' hk1 hk2 => ?_⟩

    have hmemT : (fun g => v (g * k')) ∈ T := Submodule.subset_span ⟨k', hk1, hk2, rfl⟩
    let a : Fin (Module.finrank ℂ T) → ℂ := fun l => bT.repr ⟨_, hmemT⟩ l
    have hrepr : (fun g => v (g * k')) = fun g => ∑ l, a l * (bT l : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
      have h0 := congrArg Subtype.val (bT.sum_repr ⟨_, hmemT⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      funext g
      have := congrFun h0 g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm

    have hb1 := htr v cv cv' hb k'
    have hb2 := hsum _ (fun l => (bT l : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (fun l => hMcont _ (hbmem l)) cb cb' hcb a
    rw [← hrepr] at hb2
    have hu := huniq _ ((hMcont v hv).comp (continuous_mul_const k')) _ _ _ _ hb1 hb2
    have hfun : (fun g => cv' i9 j₀ i9' j₀' (g * k')) = ∑ l, a l • cb' l i9 j₀ i9' j₀' := by
      funext g
      have := congrFun (congrFun (congrFun (congrFun (congrFun hu i9) j₀) i9') j₀') g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      exact this
    rw [hfun]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)

  obtain ⟨cmat, k₁, hcdet, hk₁, hk₀eq⟩ := exists_eq_archRealLift3_mul_of_archComponent3_eq_one k₀
  obtain ⟨bm, om, hbup, hbpos, hom, hprod⟩ := Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero 3 (Matrix.of cmat) hcdet

  have hτ : ∀ i, (e i).re < ρ + δ := fun i => by linarith [hre i]
  have hFequi : Equi ν (c' i9 j₀ i9' j₀') :=
    doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top ω w (h1 w hw).2.2.1 (h1 w hw).2.2.2 (h12 w hw)
      (h1 w hw).1 lam₁ hC1 n J e he (ρ + δ) hτ c hcc hce c' hc'c hc'e i9 i9' j₀ j₀' hbot₁ hbot₂ htop₁ htop₂
  have hFgood : Good (c' i9 j₀ i9' j₀') := ⟨w, hw, ⟨hC1, hC2, hC3⟩, c, c', ⟨hcc, hce, hc'c, hc'e⟩, rfl, hFequi⟩

  refine ⟨V, k₁, hFgood, hk₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hbdet : (Matrix.of bm).det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular (M := Matrix.of bm) (fun i j hij => hbup i j hij)]
      exact Finset.prod_ne_zero_iff.2 fun i _ => (hbpos i).ne'
    have hodet : (Matrix.of om).det ≠ 0 := by
      have h : (Matrix.of om).transpose * Matrix.of om = 1 := by
        ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; simpa [Matrix.transpose_apply, Matrix.of_apply] using hom i j
      intro h0
      have h1' := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero, Matrix.det_one] at h1'
      exact zero_ne_one h1'
    have hlift : WhittakerBlock.archRealLift3 cmat = WhittakerBlock.archRealLift3 bm * WhittakerBlock.archRealLift3 om := by
      rw [WhittakerBlock.archRealLift3_mul hbdet hodet]
      congr 1
    refine ⟨om, hom, ?_⟩
    have h := hFequi bm hbup hbpos (WhittakerBlock.archRealLift3 om * k₁)
    rw [← mul_assoc, ← hlift, ← hk₀eq] at h
    intro h0
    rw [h0, mul_zero] at h
    exact hk₀ h
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩
    exact hb.2.2.1 i9 j₀ i9' j₀'
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩
    refine ⟨?_, hEigCoeff v hv hev cv cv' hb⟩
    exact isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite ν _ (hb.2.2.1 i9 j₀ i9' j₀')
      hq (hFin v hv cv cv' hb)
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩
    exact hq
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩ k' hk1 hk2
    refine ⟨fun g => v (g * k'), h4 v hv k' hk1 hk2, ?_, fun i j y k => cv i j y (k * k'),
      fun i j i' j' k => cv' i j i' j' (k * k'), htr v cv cv' hb k', rfl, hq.translate k'⟩
    have hcas := casimir_translateRight v (h1 v hv).1 k'
    have ht : SlabL2.translateRight k' v = fun g => v (g * k') := rfl
    rw [ht] at hcas
    refine ⟨?_, ?_, ?_⟩
    · rw [hcas.1, hev.1]; rfl
    · rw [hcas.2.1, hev.2.1]; rfl
    · rw [hcas.2.2, hev.2.2]; rfl
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩
    exact hFin v hv cv cv' hb
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩ c₀ d₀
    obtain ⟨dv, dv', hdb, hflow, hD⟩ := hDdata v hv cv cv' hb c₀ d₀
    obtain ⟨hcomm, -⟩ := casimir_archDeriv_and_comm v (h1 v hv).1
    refine ⟨dv' i9 j₀ i9' j₀', ⟨archDeriv c₀ d₀ v, h5 v hv c₀ d₀, ?_, dv, dv', hdb, rfl, hq.of_hasDerivAt _ hflow⟩, hflow⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [(hcomm c₀ d₀).1, hev.1, AsmAux.D_smul]
    · rw [(hcomm c₀ d₀).2.1, hev.2.1, AsmAux.D_smul]
    · rw [(hcomm c₀ d₀).2.2, hev.2.2, AsmAux.D_smul]
  ·
    rintro G ⟨v, hv, hev, cv, cv', hb, rfl, hq⟩
    exact ⟨v, hv, cv, cv', hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, rfl⟩

end S_LanglandsTunnell_CubicInduction_exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top (solution)
