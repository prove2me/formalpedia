-- Prove2me | solution 1 for GroundTheory.Global.summable_norm_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.600182+00:00
-- url     : https://prove2.me/submissions/52bcfa6d-8447-4bd0-abca-2e6a282914a6

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
theorem _root_.solution (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (x : E) : Summable fun ℓ : Λ => ‖g (x + ℓ)‖ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g ‖x‖
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hb ℓ x le_rfl)
end GroundTheory.Global
