-- Prove2me | solution 1 for GroundTheory.Global.exists_norm_le_inv_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.844108+00:00
-- url     : https://prove2.me/submissions/5b7eb351-6f1e-448f-83c3-b580af1e7d32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic

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
omit [FiniteDimensional ℝ E]
namespace GroundTheory.Global
theorem _root_.solution (g : 𝓢(E, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g), by positivity,
    fun x => ?_⟩
  have h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa using this
end GroundTheory.Global
