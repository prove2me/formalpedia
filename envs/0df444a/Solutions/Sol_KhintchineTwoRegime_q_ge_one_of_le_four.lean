-- Prove2me | solution 1 for KhintchineTwoRegime.q_ge_one_of_le_four
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:03:56.819796+00:00
-- url     : https://prove2.me/submissions/639efbca-5ca7-413c-8e70-61ae0dfba6a6

import Mathlib
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_pad

theorem KhintchineTwoRegime.q_ge_one_of_le_four (n : ℕ) (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (ω : Fin n → ℝ) (hω : KhintchineTwoRegime.IsProper ω) :
    1 ≤ KhintchineTwoRegime.pad ω 0 + KhintchineTwoRegime.pad ω 1 := by
  obtain ⟨hA, hnn, hn⟩ := hω
  unfold HighDimProb.SparseRecovery.l2Norm at hn
  have hs : ∑ i, ω i ^ 2 = 1 := Real.sqrt_eq_one.mp hn
  interval_cases n
  · have h01 := hA (show (0:Fin 2) ≤ 1 by decide)
    have := hnn 0; have := hnn 1
    simp [KhintchineTwoRegime.pad, Fin.sum_univ_succ] at hs h01 ⊢
    nlinarith
  · have h01 := hA (show (0:Fin 3) ≤ 1 by decide)
    have h12 := hA (show (1:Fin 3) ≤ 2 by decide)
    have := hnn 0; have := hnn 1; have := hnn 2
    simp [KhintchineTwoRegime.pad, Fin.sum_univ_succ] at hs h01 h12 ⊢
    nlinarith
  · have h01 := hA (show (0:Fin 4) ≤ 1 by decide)
    have h12 := hA (show (1:Fin 4) ≤ 2 by decide)
    have h23 := hA (show (2:Fin 4) ≤ 3 by decide)
    have := hnn 0; have := hnn 1; have := hnn 2; have := hnn 3
    simp [KhintchineTwoRegime.pad, Fin.sum_univ_succ] at hs h01 h12 h23 ⊢
    nlinarith


theorem solution (n : ℕ) (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (ω : Fin n → ℝ) (hω : KhintchineTwoRegime.IsProper ω) :
    1 ≤ KhintchineTwoRegime.pad ω 0 + KhintchineTwoRegime.pad ω 1 :=
  KhintchineTwoRegime.q_ge_one_of_le_four n hn₂ hn₄ ω hω
