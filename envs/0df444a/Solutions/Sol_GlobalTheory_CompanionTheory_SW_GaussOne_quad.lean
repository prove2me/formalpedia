-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:19:00.394149+00:00
-- url     : https://prove2.me/submissions/313b00c2-5725-41c0-ba52-2b1f423fe9b4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_bil

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussOne
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.GaussOne
theorem _root_.solution {g S P : Matrix ι ι ℝ} {e : ι → ℝ} (hS : gᵀ * S * g = Matrix.diagonal e)
    (hP : gᵀ * P * g = 1) (τ : ℂ) (u : ι → ℝ) :
    (Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ u)) : ℝ) : ℂ)
        - (Real.pi : ℂ) * (τ.im : ℂ) * (((g *ᵥ u) ⬝ᵥ (P *ᵥ (g *ᵥ u)) : ℝ) : ℂ)
      = -∑ i, ((Real.pi : ℂ) * beta τ (e i)) * (u i : ℂ) ^ 2 := by
  rw [bil, bil, hS, hP]
  simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.one_mulVec]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [beta]
  ring
end GlobalTheory.CompanionTheory.SW.GaussOne
