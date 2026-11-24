-- Prove2me | solution 1 for GlobalTheory.DirichletDeriv.rpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:42.527946+00:00
-- url     : https://prove2.me/submissions/2926ec20-a183-4324-8b61-22bac5ce4136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletDeriv
namespace GlobalTheory.DirichletDeriv
theorem _root_.solution {q n : ℕ} (hn : 1 ≤ n) (hnq : n ≤ q) {x : ℝ}
    (hx : 1 - 2 / Real.log (3 * q) ≤ x) : (n : ℝ) ^ (-x) ≤ Real.exp 2 * (n : ℝ)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnq' : (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hL : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hl : Real.log n ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have h1 : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (2 / Real.log (3 * q) + (-1)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  refine h1.trans ?_
  rw [Real.rpow_add (by linarith), Real.rpow_neg_one]
  gcongr
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, div_le_iff₀ hL]
  linarith
end GlobalTheory.DirichletDeriv
