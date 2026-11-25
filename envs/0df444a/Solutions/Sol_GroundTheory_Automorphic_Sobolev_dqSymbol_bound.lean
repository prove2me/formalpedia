-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.dqSymbol_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:48.216794+00:00
-- url     : https://prove2.me/submissions/648de0ca-938d-434a-b234-a55dfb00d2a2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_dqSymbol_le

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (v : E) (t : ℝ) (ξ : E) :
    ‖dqSymbol v t ξ‖ ≤ (2 * Real.pi * ‖v‖) * (1 + ‖ξ‖ ^ 2) ^ ((s + 1 - s) / 2) := by
  refine (norm_dqSymbol_le v t ξ).trans ?_
  rw [show (s + 1 - s) / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
  have h : |inner ℝ ξ v| ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) :=
    calc |inner ℝ ξ v| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
      _ = ‖v‖ * ‖ξ‖ := mul_comm _ _
      _ ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) := by
          gcongr
          exact Real.le_sqrt_of_sq_le (by linarith)
  calc 2 * Real.pi * |inner ℝ ξ v| ≤ 2 * Real.pi * (‖v‖ * √(1 + ‖ξ‖ ^ 2)) := by gcongr
    _ = _ := by ring
end GroundTheory.Automorphic.Sobolev
