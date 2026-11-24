-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Count.one_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:55.823678+00:00
-- url     : https://prove2.me/submissions/2341ee76-711f-4d7a-887e-aa2296d5ef85

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultiDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBound
import Theorems.Thm_GlobalTheory_CompanionTheory_Count_one_dim_nat

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
theorem _root_.solution (b : ℝ) (hb : 0 < b) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 * b) := by
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) with hf
  have hsplit : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    HasSum.of_nat_of_neg_add_one ENNReal.summable.hasSum ENNReal.summable.hasSum
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have h0 : f ((0 : ℕ) : ℤ) = 1 := by simp [hf]
  have hN := one_dim_nat b hb
  have hz : ∑' n : ℕ, f n ≤ 1 + ENNReal.ofReal b := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', h0, add_comm]
      gcongr
      calc ∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℤ)
          ≤ ∑' k : ℕ, f ((k + 1 : ℕ) : ℤ) := ENNReal.sum_le_tsum _
        _ ≤ ENNReal.ofReal b := by rw [tsum_congr hpos]; exact hN
  rw [hsplit.tsum_eq, tsum_congr hneg]
  calc _ ≤ 1 + ENNReal.ofReal b + ENNReal.ofReal b := add_le_add hz hN
    _ = ENNReal.ofReal (1 + 2 * b) := by
      rw [two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) hb.le,
        ENNReal.ofReal_add (by norm_num) hb.le, ENNReal.ofReal_one]
end GlobalTheory.CompanionTheory.Count
