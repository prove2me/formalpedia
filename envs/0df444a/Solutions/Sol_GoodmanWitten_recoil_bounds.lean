-- Prove2me | solution 1 for GoodmanWitten.recoil_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:04.73306+00:00
-- url     : https://prove2.me/submissions/37f61439-ac5a-4467-a318-82b7b37b73bd

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (u u' V : EuclideanSpace ℝ (Fin 3))
    (hmom : m • u = m • u' + M • V)
    (hen : m / 2 * ‖u‖ ^ 2 = m / 2 * ‖u'‖ ^ 2 + M / 2 * ‖V‖ ^ 2) :
    ‖M • V‖ ≤ maxRecoilMomentum m ‖u‖ ∧
      M / 2 * ‖V‖ ^ 2 ≤ maxRecoilEnergy m M ‖u‖ := by
  have h1 : m • u' = m • u - M • V := by rw [hmom]; abel
  have h2 : ‖m • u'‖ ^ 2 = ‖m • u‖ ^ 2 - 2 * inner ℝ (m • u) (M • V) + ‖M • V‖ ^ 2 := by
    rw [h1, norm_sub_sq_real]
  rw [norm_smul, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_of_nonneg hm.le, Real.norm_of_nonneg hM.le] at h2
  have hcs := real_inner_le_norm u V
  have h3 : M * ((m + M) * ‖V‖ ^ 2 - 2 * m * inner ℝ u V) = 0 := by
    linear_combination -h2 - 2 * m * hen
  have h4 : (m + M) * ‖V‖ ^ 2 = 2 * m * inner ℝ u V := by
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · linarith
  have hV0 := norm_nonneg V
  have hu0 := norm_nonneg u
  have h5 : M * ‖V‖ ≤ 2 * m * ‖u‖ := by
    rcases hV0.lt_or_eq with hV | hV
    · have : (m + M) * ‖V‖ ^ 2 ≤ 2 * m * ‖u‖ * ‖V‖ := by nlinarith
      have : (m + M) * ‖V‖ ≤ 2 * m * ‖u‖ := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith
    · rw [← hV]; nlinarith
  constructor
  · rw [norm_smul, Real.norm_of_nonneg hM.le]; unfold maxRecoilMomentum; linarith
  · unfold maxRecoilEnergy
    rw [le_div_iff₀ (by positivity)]
    have : (M * ‖V‖) ^ 2 ≤ (2 * m * ‖u‖) ^ 2 := pow_le_pow_left₀ (by positivity) h5 2
    nlinarith
