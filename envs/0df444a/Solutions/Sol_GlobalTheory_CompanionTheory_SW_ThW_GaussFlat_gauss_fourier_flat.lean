-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:19.071396+00:00
-- url     : https://prove2.me/submissions/10879c86-12fe-4c52-a686-502eb49e8199

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_integral_cur
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_dot_DM
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_gauss_fourier


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  intro F _ _ ι _ _ _ M B ρ P hQ τ hτ y
  have h := (GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P hQ τ hτ).2.2.2 (cur y)
  rw [← h, ← integral_cur (F := F) (ι := ι) (fun z => gauss B ρ P τ z *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, z w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) : ℝ) : ℂ)))]
  simp only [dot_DM]
end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
