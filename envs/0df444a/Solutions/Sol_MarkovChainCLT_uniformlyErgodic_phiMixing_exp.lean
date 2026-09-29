-- Prove2me | solution 1 for MarkovChainCLT.uniformlyErgodic_phiMixing_exp
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T17:56:15.180219+00:00
-- url     : https://prove2.me/submissions/f020a3fc-c13a-4656-8308-e0ff98636690

import Theorems.Thm_MarkovChainCLT_phiMixingCoef_le_of_tvDist_le
import Definitions.Def_MarkovErgodicity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π) :
    ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
      phiMixingCoef (chainMeasure P π) (fun i ω => ω i) n ≤ c * Real.exp (-θ * n) := by
  obtain ⟨R, t, hR0, ht0, ht1, hrate⟩ := huni
  rcases eq_or_lt_of_le ht0 with htz | htpos
  · -- t = 0 : the chain is exactly π after one step
    refine ⟨R, 1, hR0, one_pos, fun n hn => ?_⟩
    refine le_trans (phiMixingCoef_le_of_tvDist_le P π hP.1 n hn 0 le_rfl (fun x => ?_)) ?_
    · have := hrate x n hn
      simpa [← htz, zero_pow (by omega : n ≠ 0)] using this
    · positivity
  · -- 0 < t < 1 : take θ = -log t
    refine ⟨R, -Real.log t, hR0, by simpa using Real.log_neg htpos ht1, fun n hn => ?_⟩
    have hpow : R * t ^ n = R * Real.exp (-(-Real.log t) * (n : ℝ)) := by
      congr 1
      rw [neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log htpos]
    rw [← hpow]
    exact phiMixingCoef_le_of_tvDist_le P π hP.1 n hn (R * t ^ n) (by positivity) (fun x => hrate x n hn)
