-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Count.one_dim_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:49.058157+00:00
-- url     : https://prove2.me/submissions/ea20b44d-1740-4c78-a357-2c97369279e4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultiDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBound
import Theorems.Thm_GlobalTheory_CompanionTheory_Count_one_dim_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Count
namespace GlobalTheory.CompanionTheory.Count
theorem _root_.solution (b : ℝ) (hb : 0 < b) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹ ≤ b - b ^ 2 / (b + N) := by
  induction N with
  | zero =>
    have : b ^ 2 / (b + ((0 : ℕ) : ℝ)) = b := by
      simp only [Nat.cast_zero, add_zero]; field_simp
    rw [Finset.range_zero, Finset.sum_empty, this, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := one_dim_step b N hb (Nat.cast_nonneg N)
    push_cast
    have e : b + ((N : ℝ) + 1) = b + N + 1 := by ring
    rw [e]
    linarith
end GlobalTheory.CompanionTheory.Count
