-- Prove2me | solution 1 for LL_Decomp1537b.abs_I1_sub
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:17.745208+00:00
-- url     : https://prove2.me/submissions/97641885-ada9-4093-a248-764ab2509325

import Mathlib
import Definitions.Def_LL_Decomp1537b_I1

open Finset Real

theorem solution (N N1 : ℕ) (h : ℤ) :
    |(LL_Decomp1537b.I1 N N1 h : ℝ) - N| ≤ |(h : ℝ)| + N1 + 1 := by
  have hup : LL_Decomp1537b.I1 N N1 h ≤ N := by
    unfold LL_Decomp1537b.I1
    calc _ ≤ #(Ioo N1 N) := card_le_card (filter_subset _ _)
      _ ≤ N := by rw [Nat.card_Ioo]; omega
  have hlow : N ≤ LL_Decomp1537b.I1 N N1 h + N1 + 1 + h.natAbs := by
    have hsub : Ioo (N1 + h.toNat) (N - (-h).toNat) ⊆
        (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N) := by
      intro m hm
      simp only [mem_Ioo, mem_filter] at hm ⊢
      omega
    have := card_le_card hsub
    rw [Nat.card_Ioo] at this
    unfold LL_Decomp1537b.I1
    omega
  have h1 : ((LL_Decomp1537b.I1 N N1 h : ℕ) : ℝ) ≤ N := by exact_mod_cast hup
  have h2 : (N : ℝ) ≤ (LL_Decomp1537b.I1 N N1 h : ℕ) + N1 + 1 + h.natAbs := by exact_mod_cast hlow
  have h3 : |(h : ℝ)| = (h.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h3, abs_le]
  constructor <;> linarith [(Nat.cast_nonneg N1 : (0 : ℝ) ≤ N1), (Nat.cast_nonneg h.natAbs : (0:ℝ) ≤ h.natAbs)]
