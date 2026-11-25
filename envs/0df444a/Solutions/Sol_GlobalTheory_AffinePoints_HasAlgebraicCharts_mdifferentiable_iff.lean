-- Prove2me | solution 1 for GlobalTheory.AffinePoints.HasAlgebraicCharts.mdifferentiable_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:23.051828+00:00
-- url     : https://prove2.me/submissions/51e15059-f097-4da9-aa88-c8ce2c8f86d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_contMDiff_eval
import Theorems.Thm_GlobalTheory_AffinePoints_mdifferentiableAt_pi_of_forall
import Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_exists_extChartAt_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
variable [CompleteSpace 𝕜]
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
namespace GlobalTheory.AffinePoints
namespace HasAlgebraicCharts
theorem _root_.solution (h : HasAlgebraicCharts 𝕜 A d)
    {φ : M → (A →ₐ[𝕜] 𝕜)} :
    letI := h.chartedSpace
    MDifferentiable I 𝓘(𝕜, Fin d → 𝕜) φ ↔ ∀ a, MDifferentiable I 𝓘(𝕜) fun m => φ m a := by
  letI := h.chartedSpace
  refine ⟨fun hφ a => ((h.contMDiff_eval a).mdifferentiable (by simp)).comp hφ, fun hφ m => ?_⟩
  have hcont : Continuous φ := GlobalTheory.AffinePoints.continuous_iff.2 fun a => (hφ a).continuous
  obtain ⟨x, s, hs, hev⟩ := h.exists_extChartAt_eventuallyEq (m := m) hcont.continuousAt
  rw [mdifferentiableAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  have hq : MDifferentiableAt I 𝓘(𝕜, Fin d → 𝕜) (fun m' i => φ m' (x i) / φ m' s) m :=
    mdifferentiableAt_pi_of_forall fun i => ((hφ (x i)) m).div ((hφ s) m) hs
  exact hq.congr_of_eventuallyEq hev
end HasAlgebraicCharts
end GlobalTheory.AffinePoints
