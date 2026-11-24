-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.derSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:49:07.769857+00:00
-- url     : https://prove2.me/submissions/0c4c21d1-8a00-4451-8b2d-ffcc85cd59cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros

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
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution (c : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeries (LSeries.logMul^[k] (c * fun n : ℕ => ((Λ n : ℝ) : ℂ))) s
      = k.factorial * derSeries c k s := by
  have h : ∀ (f : ℕ → ℂ) (k n : ℕ), (LSeries.logMul^[k] f) n = (Complex.log n) ^ k * f n := by
    intro f k n
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', LSeries.logMul, ih]; ring
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [derSeries, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, h, cpow_neg, ← Complex.natCast_log, Pi.mul_apply]
    field_simp
end GlobalTheory.LogDerivHigher
