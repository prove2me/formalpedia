-- Prove2me | solution 1 for GlobalTheory.JetConj.wr_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:25:56.883693+00:00
-- url     : https://prove2.me/submissions/af812af6-b963-4855-86a1-a23d7dfc6f16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_JetConj_wr_mul
import Theorems.Thm_GlobalTheory_JetConj_JetRel_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
namespace GlobalTheory.JetConj
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    wr (fun w => f w ^ k) z * f z ^ 2 = k * (f z ^ k) ^ 2 * wr f z := by
  induction k with
  | zero => simp [wr]
  | succ k ih =>
    simp only [pow_succ (n := k)]
    rw [wr_mul (hf.fun_pow k) hf]
    push_cast
    linear_combination f z ^ 2 * ih
end GlobalTheory.JetConj
