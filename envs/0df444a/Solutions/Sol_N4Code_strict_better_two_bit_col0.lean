-- Prove2me | solution 1 for N4Code.strict_better_two_bit_col0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:58.457153+00:00
-- url     : https://prove2.me/submissions/2763a3d3-ee2e-4b5b-8733-d230055aa6c6

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_flipCol
import Theorems.Thm_N4Code_strict_better_flip

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (_h0 : C t = col0)
    (s₀ : Column)
    (hs₀ : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 ∨
      colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12)
    (hstrict : UniversalStrictBetter (replaceColumn C t s₀) C) :
    ∃ s' : Column, (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
      UniversalStrictBetter (replaceColumn C t s') C := by
  by_cases hle : colVal s₀ ≤ 7
  · have hs₀' : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 := by
      rcases hs₀ with h3 | h5 | h6 | h9 | h10 | h12
      · simp [h3] at hle ⊢
      · simp [h5] at hle ⊢
      · simp [h6] at hle ⊢
      · simp [h9] at hle ⊢
      · simp [h10] at hle ⊢
      · simp [h12] at hle ⊢
    exact ⟨s₀, hs₀', hstrict⟩
  · have hs₀' : colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12 := by
      rcases hs₀ with h3 | h5 | h6 | h9 | h10 | h12
      · simp [h3] at hle ⊢
      · simp [h5] at hle ⊢
      · simp [h6] at hle ⊢
      · simp [h9] at hle ⊢
      · simp [h10] at hle ⊢
      · simp [h12] at hle ⊢
    have hf : colVal (flipCol s₀) = 3 ∨ colVal (flipCol s₀) = 5 ∨ colVal (flipCol s₀) = 6 := by
      have hfc := colVal_flipCol s₀
      rcases hs₀' with h9 | h10 | h12
      · rw [hfc, h9]
        norm_num
      · rw [hfc, h10]
        norm_num
      · rw [hfc, h12]
        norm_num
    have hflip : UniversalStrictBetter (replaceColumn C t (flipCol s₀)) C :=
      strict_better_flip C t s₀ hstrict
    exact ⟨flipCol s₀, hf, hflip⟩
end N4Code
