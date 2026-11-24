-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:58.146642+00:00
-- url     : https://prove2.me/submissions/a3b7aa5c-6bd7-4cb6-9aa8-16329c5019ae

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
theorem _root_.solution {g S : Matrix ι ι ℝ} {e : ι → ℝ} (hS : gᵀ * S * g = Matrix.diagonal e)
    (u v : ι → ℝ) :
    2 * (Real.pi : ℂ) * Complex.I * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)
      = ∑ i, (2 * (Real.pi : ℂ) * Complex.I * (e i : ℂ) * (v i : ℂ)) * (u i : ℂ) := by
  rw [bil, hS]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end GlobalTheory.CompanionTheory.SW.GaussOne
