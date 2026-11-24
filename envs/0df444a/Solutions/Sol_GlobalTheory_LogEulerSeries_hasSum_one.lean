-- Prove2me | solution 1 for GlobalTheory.LogEulerSeries.hasSum_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:18.732415+00:00
-- url     : https://prove2.me/submissions/24293379-123c-4ffe-b5a2-b0841cf26c1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_prod_neg_log

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
theorem _root_.solution {ι : Type} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (hsum : Summable fun i => (N i : ℝ) ^ (-s.re)) :
    HasSum (fun p : ι × ℕ => c p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) *
        Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s))
      (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hn : ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ (N i : ℝ) ^ (-s.re) := fun i => by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re]
    exact mul_le_of_le_one_left (by positivity) (hc i)
  have h := hasSum_prod_neg_log (fun i => c i * ((N i : ℕ) : ℂ) ^ (-s)) (fun i => by
    refine (hn i).trans ?_
    have h2 : (2 : ℝ) ≤ N i := by exact_mod_cast hN i
    calc (N i : ℝ) ^ (-s.re) ≤ (N i : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (N i : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2)
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hn hsum)
  convert h using 2 with p
  obtain ⟨i, k⟩ := p
  have hne : ((N i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  simp only
  rw [mul_pow, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul, ← Complex.natCast_log]
  push_cast
  rw [show ((k : ℂ) + 1) * (Complex.log (N i) * -s) = -(((k : ℂ) + 1) * Complex.log (N i)) * s by ring]
  ring
end GlobalTheory.LogEulerSeries
