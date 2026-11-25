-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_fderiv_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:03.346738+00:00
-- url     : https://prove2.me/submissions/026feb93-a1f6-4c3b-8658-a415ac13a49b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (r : ℝ) (ζ : E) :
    ‖(r / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1)) • (2 • innerSL ℝ ζ)‖ ≤
      |r| * (1 + ‖ζ‖ ^ 2) ^ ((r - 1) / 2) := by
  have hp : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  have h2 : ‖2 • innerSL ℝ ζ‖ ≤ 2 * ‖ζ‖ := by
    refine norm_nsmul_le.trans ?_
    rw [innerSL_apply_norm]; norm_num
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _), abs_div,
    abs_two]
  have hζ : ‖ζ‖ ≤ (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    linarith
  have e : (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ) =
      (1 + ‖ζ‖ ^ 2) ^ ((r - 1) / 2) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  calc |r| / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * ‖2 • innerSL ℝ ζ‖
      ≤ |r| / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * (2 * ‖ζ‖) := by gcongr
    _ = |r| * ((1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * ‖ζ‖) := by ring
    _ ≤ |r| * ((1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by rw [e]
end GroundTheory.Automorphic.Sobolev
