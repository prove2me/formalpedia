-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDyadicRightApproximantsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:47:53.712359+00:00
-- url     : https://prove2.me/submissions/e346af48-3b58-4de8-bf83-3772050131bf

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (s t : NNReal) (ht : 0 < t) (hs : s ≤ t) :
    ∃ u : ℕ → NNReal,
      (∀ n, s ≤ u n ∧ ∃ i : Fin (2 ^ n + 1),
        u n = (i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ∧
      Tendsto u atTop (𝓝 s) := by
  let u (n : ℕ) : NNReal :=
    (Nat.ceil (((s / t : NNReal) : ℝ) * (2 : ℝ) ^ n) : NNReal) /
      (2 : NNReal) ^ n * t
  obtain ⟨hu, hut⟩ := AvramDividend.Classical.avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
    s t ht hs
  refine ⟨u, ?_, hut⟩
  intro n
  refine ⟨(hu n).1, ?_⟩
  let k := Nat.ceil (((s / t : NNReal) : ℝ) * (2 : ℝ) ^ n)
  have hdiv : s / t ≤ 1 := (div_le_iff₀ ht).2 (by simpa using hs)
  have hdivR : ((s / t : NNReal) : ℝ) ≤ 1 := by exact_mod_cast hdiv
  have hk : k ≤ 2 ^ n := by
    apply Nat.ceil_le.mpr
    push_cast
    simpa using mul_le_mul_of_nonneg_right hdivR (by positivity : 0 ≤ (2 : ℝ) ^ n)
  refine ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_⟩
  change (k : NNReal) / (2 : NNReal) ^ n * t =
    (k : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))
  push_cast
  ring
