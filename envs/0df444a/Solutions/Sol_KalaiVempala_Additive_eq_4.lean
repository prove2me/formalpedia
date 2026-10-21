-- Prove2me | solution 1 for KalaiVempala.Additive.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:30:47.218549+00:00
-- url     : https://prove2.me/submissions/ad2eb3c5-65c9-4326-bd11-5bb68bb3c00d

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

set_option autoImplicit false
open MeasureTheory OracleRO.ApproxFPL KalaiVempala.Additive

theorem solution {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M)
    (s : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T := by
  induction T with
  | zero => simp [prefixSum]
  | succ T ih =>
    have hP : prefixSum s (T + 1) = prefixSum s T + s (T + 1) := by
      simp only [prefixSum]
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := (hM (prefixSum s T)).2 (M (prefixSum s (T + 1))) (hM _).1
    calc ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t) ⬝ᵥ s t + M (prefixSum s (T + 1)) ⬝ᵥ s (T + 1)
        ≤ M (prefixSum s T) ⬝ᵥ prefixSum s T + M (prefixSum s (T + 1)) ⬝ᵥ s (T + 1) := by linarith
      _ ≤ M (prefixSum s (T + 1)) ⬝ᵥ prefixSum s T + M (prefixSum s (T + 1)) ⬝ᵥ s (T + 1) := by linarith
      _ = M (prefixSum s (T + 1)) ⬝ᵥ prefixSum s (T + 1) := by rw [hP, dotProduct_add]
