-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:22.674897+00:00
-- url     : https://prove2.me/submissions/028c6a33-531f-4c6d-8e50-3262f6ed37d0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupportStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ScaleCont_tup_continuousSMul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ScaleCont_herm_continuousSMul
import Theorems.Thm_GlobalTheory_T_gram_fiber_measures_rmul_equivariant
import Theorems.Thm_GlobalTheory_T_gram_right_action_identities
import Theorems.Thm_GlobalTheory_T_haar_modular_character_of_continuous_action
import Theorems.Thm_GlobalTheory_T_hermitian_matrices_locally_compact_borel
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ScaleCont
namespace GlobalTheory.CompanionTheory.SW.ScaleCont
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∃ κ : GL (Fin n) (R ⊗[F] E) → ℝ≥0, Continuous κ ∧ (∀ g, κ g ≠ 0) ∧ κ 1 = 1 ∧ ∀ (g : GL (Fin n) (R ⊗[F] E)) (S S' : HermR R σ n), (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → m S' = κ g • (m S).map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm
  obtain ⟨r1, r2, r3, r4, -⟩ := id hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := k8 n M
  have hmem := (GlobalTheory.T.gram_right_action_identities F E σ hCM M J hJ R n).2.2.2.1
  letI a1 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tupAction
  haveI c1 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tup_continuousSMul
  obtain ⟨χ₁, hχ₁c, hχ₁⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (Fin n → Fin M → R ⊗[F] E) μ (GL (Fin n) (R ⊗[F] E))
  letI a2 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    hermAction (sigR R σ) (HermR R σ n) hmem
  haveI c2 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    herm_continuousSMul (sigR R σ) k5 (HermR R σ n) hmem
  obtain ⟨χ₂, hχ₂c, hχ₂⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (HermR R σ n) ν (GL (Fin n) (R ⊗[F] E))
  have hne : ∀ (χ : GL (Fin n) (R ⊗[F] E) →* ℝ≥0) (g), χ g ≠ 0 := by
    intro χ g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  refine ⟨fun g => χ₁ g * χ₂ g⁻¹, hχ₁c.mul (hχ₂c.comp continuous_inv), ?_, ?_, ?_⟩
  · exact fun g => mul_ne_zero (hne χ₁ g) (hne χ₂ g⁻¹)
  · simp
  · intro g S S' hS'
    let τ : HermR R σ n → HermR R σ n := fun S => g⁻¹ • S
    have hτ : ∀ S : HermR R σ n, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
          (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
      intro S
      show cT (sigR R σ) (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
        (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
      rw [inv_inv]
    have hS'τ : S' = τ S := Subtype.ext (hS'.trans (hτ S).symm)
    have hmap₁ : μ.map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = χ₁ g⁻¹ • μ := by
      have := hχ₁ g⁻¹
      have e : (fun v : Fin n → Fin M → R ⊗[F] E => g⁻¹ • v) =
          fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
        funext X
        show tupR X (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
        rw [inv_inv]
        rfl
      rwa [e] at this
    have hmap₂ : ν.map τ = χ₂ g⁻¹ • ν := hχ₂ g⁻¹
    have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hCM M J hJ R hR n μ ν m hμ hν hm
      (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Matrix.isUnits_det_units g) τ hτ
      (χ₁ g⁻¹) (χ₂ g⁻¹) hmap₁ hmap₂ S
    rw [hS'τ]
    have hinv : χ₁ g * χ₁ g⁻¹ = 1 := by rw [← map_mul]; simp
    calc m (τ S) = (χ₁ g * χ₁ g⁻¹) • m (τ S) := by rw [hinv, one_smul]
      _ = χ₁ g • (χ₁ g⁻¹ • m (τ S)) := by rw [mul_smul]
      _ = χ₁ g • (χ₂ g⁻¹ • (m S).map fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
        rw [key]
      _ = _ := by rw [mul_smul]
end GlobalTheory.CompanionTheory.SW.ScaleCont
