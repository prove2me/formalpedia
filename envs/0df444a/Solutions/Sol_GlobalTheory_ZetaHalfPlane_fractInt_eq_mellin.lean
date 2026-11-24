-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.fractInt_eq_mellin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:17.986535+00:00
-- url     : https://prove2.me/submissions/fa45422a-2a81-4ce7-b8a9-fadc49fe8764

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution (s : ℂ) : fractInt s = mellin cutFract (-s) := by
  unfold fractInt mellin cutFract
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ)) t = (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm,
        show -s - 1 = -(s + 1) by ring]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]
end GlobalTheory.ZetaHalfPlane
