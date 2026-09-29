-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2b82c096-fed8-57db-becd-c1ea1728ef97

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_sum_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_comp_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace WsB
namespace CM

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ
abbrev CV (n J : ℕ) : Type := Fin n → Fin J → ℝ → G3 → ℂ
abbrev CV' (n J : ℕ) : Type := Fin n → Fin J → Fin n → Fin J → G3 → ℂ

def HasBlock (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (v : G3 → ℂ) (cv : CV n J) (cv' : CV' n J) : Prop :=
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

section
variable {ρ : ℝ} {n J : ℕ} {e : Fin n → ℂ} {δ : ℝ}

theorem hasBlock_lincomb (v w : G3 → ℂ) (hv : Continuous v) (hw : Continuous w)
    (cv cw : CV n J) (cv' cw' : CV' n J)
    (hbv : HasBlock ρ n J e δ v cv cv') (hbw : HasBlock ρ n J e δ w cw cw') (a b : ℂ) :
    HasBlock ρ n J e δ (fun g => a * v g + b * w g) (fun i j y k => a * cv i j y k + b * cw i j y k)
      (fun i j i' j' k => a * cv' i j i' j' k + b * cw' i j i' j' k) := by
  have hc : ∀ l : Fin 2, Continuous (![v, w] l) := by
    intro l; fin_cases l
    · exact hv
    · exact hw
  have hb : ∀ l : Fin 2, HasBlock ρ n J e δ (![v, w] l) (![cv, cw] l) (![cv', cw'] l) := by
    intro l; fin_cases l
    · exact hbv
    · exact hbw
  have h := LanglandsTunnell.CubicInduction.joint_expansion_sum_mul ρ n J e δ 2 ![v, w] hc ![cv, cw] ![cv', cw']
    hb ![a, b]
  have e1 : (fun g : G3 => ∑ l : Fin 2, ![a, b] l * ![v, w] l g) = fun g => a * v g + b * w g := by
    funext g; simp [Fin.sum_univ_two]
  have e2 : (fun (i : Fin n) (j : Fin J) (y : ℝ) (k : G3) => ∑ l : Fin 2, ![a, b] l * ![cv, cw] l i j y k) =
      fun i j y k => a * cv i j y k + b * cw i j y k := by
    funext i j y k; simp [Fin.sum_univ_two]
  have e3 : (fun (i : Fin n) (j : Fin J) (i' : Fin n) (j' : Fin J) (k : G3) =>
      ∑ l : Fin 2, ![a, b] l * ![cv', cw'] l i j i' j' k) =
      fun i j i' j' k => a * cv' i j i' j' k + b * cw' i j i' j' k := by
    funext i j i' j' k; simp [Fin.sum_univ_two]
  rw [e1, e2, e3] at h
  exact h

theorem hasBlock_translate (v : G3 → ℂ) (cv : CV n J) (cv' : CV' n J) (hb : HasBlock ρ n J e δ v cv cv') (k' : G3) :
    HasBlock ρ n J e δ (fun g => v (g * k')) (fun i j y k => cv i j y (k * k')) (fun i j i' j' k => cv' i j i' j' (k * k')) :=
  LanglandsTunnell.CubicInduction.joint_expansion_comp_mul_right ρ n J e δ v cv cv' hb k'

theorem W_zero (g : G3) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ (fun _ : G3 => (0 : ℂ)) g = 0 := by
  simp [whittaker3]

theorem cv'_unique (hδ : 0 < δ) (he : Function.Injective e) (hre : ∀ i, (e i).re ≤ ρ)
    (v : G3 → ℂ) (hv : Continuous v) (cv₁ cv₂ : CV n J) (cv₁' cv₂' : CV' n J)
    (h₁ : HasBlock ρ n J e δ v cv₁ cv₁') (h₂ : HasBlock ρ n J e δ v cv₂ cv₂') :
    cv₁' = cv₂' := by
  have h := hasBlock_lincomb v v hv hv cv₁ cv₂ cv₁' cv₂' h₁ h₂ 1 (-1)
  have e0 : (fun g : G3 => (1 : ℂ) * v g + (-1) * v g) = fun _ => (0 : ℂ) := by funext g; ring
  rw [e0] at h
  funext i j i' j' k
  have hu := LanglandsTunnell.CubicInduction.joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero
    (fun _ : G3 => (0 : ℂ)) ρ n J e δ hδ he hre (fun i j y k => 1 * cv₁ i j y k + -1 * cv₂ i j y k)
    (fun i j i' j' k => 1 * cv₁' i j i' j' k + -1 * cv₂' i j i' j' k) h k (fun y₁ y₂ _ _ => W_zero _)
  have := hu.2 i j i' j'
  have : (1 : ℂ) * cv₁' i j i' j' k + (-1) * cv₂' i j i' j' k = 0 := this
  linear_combination this

end

end WsB.CM

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

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
    (i9 i9' : Fin n) (j₀ j₀' : Fin J) :
    ∃ Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
        (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
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
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) →
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ k = cv' i9 j₀ i9' j₀' k) ∧
      (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k')) ∧
      (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0) := by
  classical

  have hexist : ∀ v : ↥M, ∃ p : WsB.CM.CV n J × WsB.CM.CV' n J,
      WsB.CM.HasBlock ρ n J e δ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) p.1 p.2 := by
    intro v
    obtain ⟨N, hN⟩ := h13 v v.2
    obtain ⟨c, hc1, hc2, c', hc'1, hc'2, -⟩ := (hexp N v (h1 v v.2).2.2.1 (h1 v v.2).2.2.2 (h12 v v.2)
      (h1 v v.2).1 (h3 v v.2) (hrel v v.2).1 (hrel v v.2).2 hN).1
    exact ⟨(c, c'), hc1, hc2, hc'1, hc'2⟩
  choose blk hblk using hexist
  have hcont : ∀ v : ↥M, Continuous (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := fun v => by
    simpa using (h1 v v.2).2.2.1 []
  have huniq : ∀ (v : ↥M) (cv : WsB.CM.CV n J) (cv' : WsB.CM.CV' n J),
      WsB.CM.HasBlock ρ n J e δ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) cv cv' → (blk v).2 = cv' :=
    fun v cv cv' hb => WsB.CM.cv'_unique hδ he hre _ (hcont v) _ _ _ _ (hblk v) hb
  let Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    { toFun := fun v => (blk v).2 i9 j₀ i9' j₀'
      map_add' := by
        intro v w
        have hb := WsB.CM.hasBlock_lincomb (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
          (hcont v) (hcont w) _ _ _ _ (hblk v) (hblk w) 1 1
        have e1 : (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 : ℂ) * (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g +
            1 * (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g) = ((v + w : ↥M) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
          funext g; simp
        rw [e1] at hb
        rw [huniq (v + w) _ _ hb]
        funext k
        simp
      map_smul' := by
        intro c v
        have hb := WsB.CM.hasBlock_lincomb (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
          (hcont v) (hcont v) _ _ _ _ (hblk v) (hblk v) c 0
        have e1 : (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => c * (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g +
            0 * (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g) = ((c • v : ↥M) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
          funext g; simp
        rw [e1] at hb
        rw [huniq (c • v) _ _ hb]
        funext k
        simp }
  refine ⟨Λ, ?_, ?_, ?_⟩
  · intro v hv cv cv' hb k
    show (blk ⟨v, hv⟩).2 i9 j₀ i9' j₀' k = cv' i9 j₀ i9' j₀' k
    rw [huniq ⟨v, hv⟩ cv cv' hb]
  · intro v hv k' hk'₁ hk'₂ g
    show (blk ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩).2 i9 j₀ i9' j₀' g = (blk ⟨v, hv⟩).2 i9 j₀ i9' j₀' (g * k')
    have hb := WsB.CM.hasBlock_translate v _ _ (hblk ⟨v, hv⟩) k'
    rw [huniq ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ _ _ hb]
  · intro v hv c d g
    show HasDerivAt
      (fun s : ℝ => (blk ⟨v, hv⟩).2 i9 j₀ i9' j₀' (g * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
      ((blk ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩).2 i9 j₀ i9' j₀' g) 0
    exact LanglandsTunnell.CubicInduction.hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
      v (h1 v hv) c d ρ n J e δ hδ he hre (blk ⟨v, hv⟩).1 (blk ⟨v, hv⟩).2 (hblk ⟨v, hv⟩)
      (blk ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩).1 (blk ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩).2
      (hblk ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩) i9 j₀ i9' j₀' g

end
end S_LanglandsTunnell_CubicInduction_exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_doubleSlotCoeff_of_smoothingSubmodule (solution)
