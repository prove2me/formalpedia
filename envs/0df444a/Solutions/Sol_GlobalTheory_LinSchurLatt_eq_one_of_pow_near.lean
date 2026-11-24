-- Prove2me | solution 1 for GlobalTheory.LinSchurLatt.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:10.735365+00:00
-- url     : https://prove2.me/submissions/01557fa2-7b9a-466c-be49-5d80561e2c5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.LinSchurLatt
namespace GlobalTheory.LinSchurLatt
theorem _root_.solution (z : ℂ) (h : ∀ m : ℕ, ‖z ^ m - 1‖ ≤ 1 / 2) : z = 1 := by
  have hre : ∀ m : ℕ, 1 / 2 ≤ (z ^ m).re := by
    intro m
    have h1 := (Complex.abs_re_le_norm (z ^ m - 1)).trans (h m)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_le.1 h1).1]
  have hS : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ m ∈ Finset.range N, z ^ m‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ m ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun m _ => hre m
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have e := geom_sum_mul z N
  have h2 : ‖z - 1‖ * ((N : ℝ) / 2) ≤ 1 / 2 := by
    calc ‖z - 1‖ * ((N : ℝ) / 2) ≤ ‖z - 1‖ * ‖∑ m ∈ Finset.range N, z ^ m‖ :=
          mul_le_mul_of_nonneg_left (hS N) hpos.le
      _ = ‖z ^ N - 1‖ := by rw [← e, norm_mul, mul_comm]
      _ ≤ 1 / 2 := h N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith
end GlobalTheory.LinSchurLatt
