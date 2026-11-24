-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.norm_pow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:54.71146+00:00
-- url     : https://prove2.me/submissions/bda91584-f2e7-4c97-8c1a-3d3954bc6e35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (j : ℕ) :
    ‖a ^ j - b ^ j‖ ≤ j * ‖a - b‖ := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    have hbn : ‖b ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖a‖ * ‖a ^ n - b ^ n‖ ≤ ‖a ^ n - b ^ n‖ := mul_le_of_le_one_left (norm_nonneg _) ha
    have h2 : ‖b ^ n‖ * ‖a - b‖ ≤ ‖a - b‖ := mul_le_of_le_one_left (norm_nonneg _) hbn
    push_cast
    linarith
end GlobalTheory.Lin.Repulsion
