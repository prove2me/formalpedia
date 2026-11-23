-- Prove2me | solution 1 for KhintchineTwoRegime.proper_unit_distance_sq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:04:08.248856+00:00
-- url     : https://prove2.me/submissions/82e4e890-a88f-4799-ba03-88dc28f4aa5f

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_pad

theorem KhintchineTwoRegime.proper_unit_distance_sq (n : ℕ) (hn : 2 ≤ n) (τ : ℝ)
    (ω : Fin n → ℝ) (hω : ω ∈ KhintchineTwoRegime.Cn n τ) :
    τ ^ 2 = 2 - Real.sqrt 2 *
      (KhintchineTwoRegime.pad ω 0 + KhintchineTwoRegime.pad ω 1) := by
  obtain ⟨⟨_, _, hn1⟩, hd⟩ := hω
  unfold HighDimProb.SparseRecovery.l2Norm at hn1 hd
  have hs : ∑ i, ω i ^ 2 = 1 := Real.sqrt_eq_one.mp hn1
  have hsum_nonneg : 0 ≤ ∑ i, (ω - KhintchineTwoRegime.omegaStar n) i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← hd, Real.sq_sqrt hsum_nonneg]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 2 ≠ 0 := by positivity
  have hinv : (1:ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by field_simp; linarith
  simp only [Fin.sum_univ_succ, Pi.sub_apply, KhintchineTwoRegime.omegaStar, KhintchineTwoRegime.pad] at hs ⊢
  simp [Fin.val_succ, hinv] at hs ⊢
  linear_combination hs + (1/2:ℝ) * h2


theorem solution (n : ℕ) (hn : 2 ≤ n) (τ : ℝ)
    (ω : Fin n → ℝ) (hω : ω ∈ KhintchineTwoRegime.Cn n τ) :
    τ ^ 2 = 2 - Real.sqrt 2 *
      (KhintchineTwoRegime.pad ω 0 + KhintchineTwoRegime.pad ω 1) :=
  KhintchineTwoRegime.proper_unit_distance_sq n hn τ ω hω
