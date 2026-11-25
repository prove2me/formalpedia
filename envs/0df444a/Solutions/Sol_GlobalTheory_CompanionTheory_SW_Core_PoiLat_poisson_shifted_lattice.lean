-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:19.013539+00:00
-- url     : https://prove2.me/submissions/1bb10ca8-6f83-42aa-b80f-f5b8a263d594

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_gaussian_lattice_term
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_gaussian_fourier
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_siegelGaussIntegral_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_fourier_lattice_term
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_phase_lattice
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_eq_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_transpose_mul_mul
import Theorems.Thm_GlobalTheory_riemannThetaTerm_zero_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.PoiLat
variable {κ : Type} [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat
theorem _root_.solution : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ), Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ, let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))); let fh : (κ → ℝ) → ℂ := fun y => ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)); Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧ Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧ ∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = ((|g.det|⁻¹ : ℝ) : ℂ) * ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) = GlobalTheory.siegelGaussIntegral Z *
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) = GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def, ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0
end GlobalTheory.CompanionTheory.SW.Core.PoiLat
