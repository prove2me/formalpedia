-- Prove2me | solution 1 for GlobalTheory.normSq_geomSum_le_fejer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:45.969455+00:00
-- url     : https://prove2.me/submissions/b93b4d6f-c31c-4ff5-bed7-cfe87afa7046

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    Complex.normSq (∑ j ∈ Finset.range (J + 1), w ^ j) ≤
      (J + 1 : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re := by
  have hre : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), w ^ j).re
      = 1 + ∑ j ∈ Finset.Icc 1 n, (w ^ j).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Complex.add_re, ih, Finset.sum_Icc_succ_top (by omega)]
      ring
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : ∑ j ∈ Finset.range (J + 1 + 1), w ^ j
        = w * (∑ j ∈ Finset.range (J + 1), w ^ j) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ']
    have h2 : ∑ j ∈ Finset.Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (w ^ j).re
        = ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re
          + ∑ j ∈ Finset.Icc 1 (J + 1), (w ^ j).re := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      · push_cast; ring
    have h3 := hre (J + 1)
    have hw2 : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg w
      nlinarith
    rw [h2]
    set S := ∑ j ∈ Finset.range (J + 1), w ^ j
    rw [h1] at h3 ⊢
    have h4 : Complex.normSq (w * S + 1) = Complex.normSq w * Complex.normSq S
        + 2 * (w * S + 1).re - 1 := by
      rw [Complex.normSq_add, map_mul]
      simp
      ring
    have h5 := Complex.normSq_nonneg S
    rw [h4, h3]
    push_cast
    nlinarith
end GlobalTheory
