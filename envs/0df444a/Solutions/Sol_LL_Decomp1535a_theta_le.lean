-- Prove2me | solution 1 for LL_Decomp1535a.theta_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:04:58.414085+00:00
-- url     : https://prove2.me/submissions/a87350b3-633d-43e6-a6bd-7231d24a9553

import Mathlib
import Definitions.Def_LL_Decomp1535a_theta

open MeasureTheory

noncomputable def GbAAux.thetaA (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

theorem GbAAux.theta_le (N : ℕ) : GbAAux.thetaA N ≤ Real.log 4 * N := by
  have h1 : GbAAux.thetaA N = Real.log (primorial N) := by
    unfold GbAAux.thetaA primorial
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
  rw [h1]
  calc Real.log (primorial N) ≤ Real.log ((4 : ℕ) ^ N : ℕ) := by
        apply Real.log_le_log
        · exact_mod_cast (primorial_pos N)
        · exact_mod_cast primorial_le_4_pow N
    _ = Real.log 4 * N := by
        rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

theorem solution (N : ℕ) :
    LL_Decomp1535a.theta N ≤ Real.log 4 * N :=
  GbAAux.theta_le N
