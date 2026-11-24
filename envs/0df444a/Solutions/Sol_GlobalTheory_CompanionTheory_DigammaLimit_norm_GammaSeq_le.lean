-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.norm_GammaSeq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:15.669753+00:00
-- url     : https://prove2.me/submissions/e01c6dbf-38a1-43f0-b98d-f7779a297470

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_euler_seq_le_Gamma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq w n‖ ≤ Real.Gamma w.re := by
  refine le_trans ?_ (euler_seq_le_Gamma hw hn)
  rw [GammaSeq, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    norm_prod, Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) (Finset.prod_pos fun j _ => by positivity)
  apply Finset.prod_le_prod (fun j _ => by positivity)
  intro j _
  have := Complex.abs_re_le_norm (w + j)
  simp only [add_re, natCast_re] at this
  exact (le_abs_self _).trans this
end GlobalTheory.CompanionTheory.DigammaLimit
