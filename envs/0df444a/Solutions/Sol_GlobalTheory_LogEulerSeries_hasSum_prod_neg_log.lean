-- Prove2me | solution 1 for GlobalTheory.LogEulerSeries.hasSum_prod_neg_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:25.62538+00:00
-- url     : https://prove2.me/submissions/26aff84c-1083-459b-a894-dc5ce6348d35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_neg_log_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.LogEulerSeries
namespace GlobalTheory.LogEulerSeries
theorem _root_.solution {ι : Type} (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2)
    (hs : Summable fun i => ‖z i‖) :
    HasSum (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1))
      (∑' i, -Complex.log (1 - z i)) := by
  have hsum : Summable (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1)) := by
    have hb : Summable (fun p : ι × ℕ => ‖z p.1‖ * ((1 / 2 : ℝ) ^ p.2)) :=
      hs.mul_of_nonneg summable_geometric_two (fun i => norm_nonneg _) (fun k => by positivity)
    refine Summable.of_norm_bounded hb ?_
    rintro ⟨i, k⟩
    simp only
    have h1 : (1 : ℝ) ≤ ‖(k : ℂ) + 1‖ := by
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.le_add_left 1 k
    rw [norm_div, norm_pow, pow_succ, mul_comm]
    calc ‖z i‖ * ‖z i‖ ^ k / ‖(k : ℂ) + 1‖ ≤ ‖z i‖ * ‖z i‖ ^ k := div_le_self (by positivity) h1
      _ ≤ ‖z i‖ * (1 / 2 : ℝ) ^ k := by gcongr; exact hz i
  have hf : ∀ i, HasSum (fun k : ℕ => z i ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z i)) :=
    fun i => hasSum_neg_log_succ (by linarith [hz i])
  have h3 := hsum.hasSum.prod_fiberwise hf
  rw [h3.tsum_eq]
  exact hsum.hasSum
end GlobalTheory.LogEulerSeries
