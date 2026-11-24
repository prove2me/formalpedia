-- Prove2me | solution 1 for GlobalTheory.AffinePoints.HasAlgebraicCharts.exists_extChartAt_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:33.637826+00:00
-- url     : https://prove2.me/submissions/ab7a7d2e-1550-4dc3-bd44-21cca3620ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth

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
omit [CompleteSpace 𝕜]
namespace GlobalTheory.AffinePoints
namespace HasAlgebraicCharts
theorem _root_.solution (h : HasAlgebraicCharts 𝕜 A d)
    {φ : M → (A →ₐ[𝕜] 𝕜)} {m : M} (hφ : ContinuousAt φ m) :
    letI := h.chartedSpace
    ∃ (x : Fin d → A) (s : A), φ m s ≠ 0 ∧
      extChartAt 𝓘(𝕜, Fin d → 𝕜) (φ m) ∘ φ =ᶠ[𝓝 m] fun m' i => φ m' (x i) / φ m' s := by
  letI := h.chartedSpace
  have hc : IsAlgebraicChart (chartAt (Fin d → 𝕜) (φ m)) := chart_mem_atlas (Fin d → 𝕜) (φ m)
  obtain ⟨x, s, hxs⟩ := hc.exists_eq_div
  have hev : ∀ᶠ m' in 𝓝 m, φ m' ∈ (chartAt (Fin d → 𝕜) (φ m)).source :=
    hφ.preimage_mem_nhds ((chartAt (Fin d → 𝕜) (φ m)).open_source.mem_nhds (mem_chart_source _ _))
  refine ⟨x, s, (hxs _ (mem_chart_source _ _)).1, ?_⟩
  filter_upwards [hev] with m' hm'
  funext i
  simp [(hxs _ hm').2 i]
end HasAlgebraicCharts
end GlobalTheory.AffinePoints
