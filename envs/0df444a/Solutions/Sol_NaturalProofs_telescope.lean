-- Prove2me | solution 1 for NaturalProofs.telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:31:30.349377+00:00
-- url     : https://prove2.me/submissions/546ad388-c1b9-4a8c-a828-ea0864248f7b

module
public import Mathlib
public import Definitions.Def_NaturalProofs_Prob

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]
namespace NaturalProofs
theorem _root_.solution (q : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ t < N, |q 0 - q N| / N ≤ |q t - q (t + 1)| := by
  by_contra h
  push Not at h
  have hsum : q 0 - q N = ∑ t ∈ range N, (q t - q (t + 1)) := (Finset.sum_range_sub' q N).symm
  have h1 : |q 0 - q N| ≤ ∑ t ∈ range N, |q t - q (t + 1)| :=
    hsum ▸ Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ t ∈ range N, |q t - q (t + 1)| < ∑ _t ∈ range N, |q 0 - q N| / N :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hN.ne')
      (fun t ht => h t (Finset.mem_range.mp ht))
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hN'] at h2
  linarith
end NaturalProofs
