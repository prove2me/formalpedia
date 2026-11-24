-- Prove2me | solution 1 for GlobalTheory.PuncturedDiscExtension.analyticAt_update_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:02.662469+00:00
-- url     : https://prove2.me/submissions/e90ee684-7f70-4420-acd8-9e1248d7ed44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.PuncturedDiscExtension
namespace GlobalTheory.PuncturedDiscExtension
theorem _root_.solution {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    (hb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B) :
    AnalyticAt ℂ (Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F)) 0 := by
  obtain ⟨B, hB⟩ := hb
  have ht : Tendsto F (𝓝[≠] (0:ℂ)) (𝓝 (limUnder (𝓝[≠] (0:ℂ)) F)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd
    refine isBoundedUnder_of_eventually_le (a := B + ‖F 0‖) ?_
    filter_upwards [hB] with z hz
    exact (norm_sub_le _ _).trans (by linarith)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · rw [eventually_nhdsWithin_iff] at hd ⊢
    filter_upwards [hd] with z hz hz0
    have heq : Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F) =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hz hz0).congr_of_eventuallyEq heq
  · exact continuousAt_update_same.2 ht
end GlobalTheory.PuncturedDiscExtension
