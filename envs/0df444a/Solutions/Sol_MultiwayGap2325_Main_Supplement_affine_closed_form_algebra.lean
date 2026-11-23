-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.affine_closed_form_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:29:57.262852+00:00
-- url     : https://prove2.me/submissions/665cb7bc-56e2-42a0-862f-57c092b2064c

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

open MultiwayGap2325.Main.Supplement
open scoped BigOperators

theorem solution (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    affineBSum q T = affineBClosed q T ∧
      affineBClosed q T - affineRClosed q T = affineNetClosed q T := by
  constructor
  · have hT : T ≠ 0 := by positivity
    have hzT : T * affineZ T = 1 - T := by
      unfold affineZ
      field_simp
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
    induction n with
    | zero =>
        norm_num [affineBSum, affineBClosed]
        linear_combination hzT
    | succ n ih =>
        have ih := ih (by omega)
        rw [show n + 1 + 2 = (n + 2) + 1 by omega]
        rw [affineBSum, Finset.sum_Icc_succ_top (by omega : 2 ≤ (n + 2) + 1)]
        rw [← affineBSum, ih]
        rw [show n + 2 + 1 = n + 3 by omega]
        simp only [show n + 3 - 2 = n + 1 by omega,
          show n + 3 - 1 = n + 2 by omega]
        unfold affineBClosed
        simp only [show n + 2 - 1 = n + 1 by omega]
        have hfac : (((n + 2).factorial : ℕ) : ℝ) =
            (n + 2 : ℝ) * (n + 1).factorial := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hfac0 : ((n + 1).factorial : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
        have hz : affineZ T ^ (n + 2) = affineZ T ^ (n + 1) * affineZ T := by
          rw [← pow_succ]
        rw [hfac]
        push_cast
        field_simp
        rw [hfac, hz]
        simp only [pow_succ]
        linear_combination
          (((n : ℝ) + 2) * ((n + 1).factorial : ℝ) * affineZ T ^ n * affineZ T) * hzT
  · have hT : T ≠ 0 := by positivity
    have hqR : (q : ℝ) ≠ 0 := by positivity
    have hfac0 : ((q - 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hfac : (q.factorial : ℝ) = q * (q - 1).factorial := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      rw [show m + 1 - 1 = m by omega, Nat.factorial_succ]
      push_cast
      ring
    have hpow : T ^ (q - 1) = T ^ (q - 2) * T := by
      rw [← pow_succ]
      congr 1
      omega
    unfold affineBClosed affineRClosed affineNetClosed affineZ
    rw [div_pow, hfac, hpow]
    field_simp
    ring
