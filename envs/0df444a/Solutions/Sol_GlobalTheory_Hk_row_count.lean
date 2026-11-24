-- Prove2me | solution 1 for GlobalTheory.Hk.row_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:06.115509+00:00
-- url     : https://prove2.me/submissions/d3400dd0-707e-4da5-a949-7d150da98803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution (α c y : ℝ) (hα : 0 < α) :
    ∃ F : Finset ℤ, (∀ m : ℤ, m ∈ F ↔ α * (m + c) ^ 2 ≤ y) ∧
      |(F.card : ℝ) - 2 * Real.sqrt (y / α)| ≤ 1 := by
  rcases lt_or_ge y 0 with hy | hy
  · refine ⟨∅, fun m => ?_, ?_⟩
    · simp only [Finset.notMem_empty, false_iff, not_le]
      have := mul_nonneg hα.le (sq_nonneg ((m : ℝ) + c))
      linarith
    · rw [Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonpos_of_nonneg hy.le hα.le)]
      simp
  · have hyα : 0 ≤ y / α := div_nonneg hy hα.le
    refine ⟨Finset.Icc ⌈-c - Real.sqrt (y / α)⌉ ⌊-c + Real.sqrt (y / α)⌋, fun m => ?_, ?_⟩
    · rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor,
        show α * ((m : ℝ) + c) ^ 2 ≤ y ↔ ((m : ℝ) + c) ^ 2 ≤ y / α by
          rw [le_div_iff₀ hα, mul_comm],
        Real.sq_le hyα]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    · have hu1 := Int.floor_le (-c + Real.sqrt (y / α))
      have hu2 := Int.lt_floor_add_one (-c + Real.sqrt (y / α))
      have hv1 := Int.le_ceil (-c - Real.sqrt (y / α))
      have hv2 := Int.ceil_lt_add_one (-c - Real.sqrt (y / α))
      have hR := Real.sqrt_nonneg (y / α)
      have hnn : 0 ≤ ⌊-c + Real.sqrt (y / α)⌋ + 1 - ⌈-c - Real.sqrt (y / α)⌉ := by
        have : ⌈-c - Real.sqrt (y / α)⌉ - 1 ≤ ⌊-c + Real.sqrt (y / α)⌋ := by
          apply Int.le_floor.mpr
          push_cast
          linarith
        linarith
      rw [Int.card_Icc]
      have hcast : (((⌊-c + Real.sqrt (y / α)⌋ + 1 - ⌈-c - Real.sqrt (y / α)⌉).toNat : ℕ) : ℝ)
          = (((⌊-c + Real.sqrt (y / α)⌋ + 1 - ⌈-c - Real.sqrt (y / α)⌉ : ℤ)) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnn
      rw [hcast]
      push_cast
      rw [abs_le]
      constructor <;> linarith
end GlobalTheory.Hk
