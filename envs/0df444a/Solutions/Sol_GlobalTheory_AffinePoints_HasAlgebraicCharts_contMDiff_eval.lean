-- Prove2me | solution 1 for GlobalTheory.AffinePoints.HasAlgebraicCharts.contMDiff_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:23.83345+00:00
-- url     : https://prove2.me/submissions/561363f2-be8e-4488-8b82-6f893b200205

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
namespace GlobalTheory.AffinePoints
namespace HasAlgebraicCharts
theorem _root_.solution (h : HasAlgebraicCharts 𝕜 A d) (a : A) :
    letI := h.chartedSpace
    ContMDiff 𝓘(𝕜, Fin d → 𝕜) 𝓘(𝕜) ω fun p : A →ₐ[𝕜] 𝕜 => p a := by
  letI := h.chartedSpace
  intro p
  have hc : IsAlgebraicChart (chartAt (Fin d → 𝕜) p) := chart_mem_atlas (Fin d → 𝕜) p
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps]
  rw [contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact (hc.analyticOnNhd a _ (mem_chart_target _ p)).contDiffAt
end HasAlgebraicCharts
end GlobalTheory.AffinePoints
