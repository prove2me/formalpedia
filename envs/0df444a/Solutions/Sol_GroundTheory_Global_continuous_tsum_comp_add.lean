-- Prove2me | solution 1 for GroundTheory.Global.continuous_tsum_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:05.604267+00:00
-- url     : https://prove2.me/submissions/aae8c8d3-70f2-4cd8-9974-22099a79bc90

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Theorems.Thm_GroundTheory_Global_exists_summable_bound_comp_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GroundTheory.Global
theorem _root_.solution [CompleteSpace F] (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] (g : 𝓢(E, F)) : Continuous fun x => ∑' ℓ : Λ, g (x + ℓ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g (‖x₀‖ + 1)
  have hc : ContinuousOn (fun x => ∑' ℓ : Λ, g (x + ℓ)) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    continuousOn_tsum (fun ℓ => (g.continuous.comp (continuous_id.add continuous_const)).continuousOn)
      hu (fun ℓ x hx => hb ℓ x (by simpa using hx))
  exact hc.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp))
end GroundTheory.Global
