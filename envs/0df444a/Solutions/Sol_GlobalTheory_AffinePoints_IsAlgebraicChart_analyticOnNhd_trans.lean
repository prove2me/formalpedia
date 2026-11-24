-- Prove2me | solution 1 for GlobalTheory.AffinePoints.IsAlgebraicChart.analyticOnNhd_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:34.393523+00:00
-- url     : https://prove2.me/submissions/42785c06-fab7-47f7-a2fd-ce5c5e2da240

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
namespace GlobalTheory.AffinePoints
namespace IsAlgebraicChart
theorem _root_.solution
    {e e' : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)} (he : IsAlgebraicChart e)
    (he' : IsAlgebraicChart e') : AnalyticOnNhd 𝕜 (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  intro z hz
  obtain ⟨x', s', hx'⟩ := he'.exists_eq_div
  have hzt : z ∈ e.target := hz.1
  have hzs : e.symm z ∈ e'.source := hz.2
  have hev : ∀ᶠ w in 𝓝 z, e.symm w ∈ e'.source :=
    (e.continuousAt_symm hzt).preimage_mem_nhds (e'.open_source.mem_nhds hzs)
  have hq : AnalyticAt 𝕜 (fun w i => e.symm w (x' i) / e.symm w s') z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (he.analyticOnNhd _ z hzt).div (he.analyticOnNhd _ z hzt) (hx' _ hzs).1
  refine hq.congr ?_
  filter_upwards [hev] with w hw
  funext i
  simp [(hx' _ hw).2 i]
end IsAlgebraicChart
end GlobalTheory.AffinePoints
