-- Prove2me | solution 1 for InvMarketMaking.LOB.proposition_6_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:23:42.85676+00:00
-- url     : https://prove2.me/submissions/a4808bd4-d5c9-419a-a27e-d0b838003183

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_lobRound

open MeasureTheory ProbabilityTheory

open InvMarketMaking.LOB in
theorem solution (vs vb bid ask : ℕ → ℝ) (t : ℕ) :
    (∀ b : ℝ, (∀ τ ∈ Finset.Icc 1 t, bid τ ≤ b) →
      estSellOf vs bid t b = (∑ τ ∈ Finset.Icc 1 t, if vs τ ≤ b then (1 : ℝ) else 0) / t) ∧
    (∀ a : ℝ, (∀ τ ∈ Finset.Icc 1 t, a ≤ ask τ) →
      estBuyOf vb ask t a = (∑ τ ∈ Finset.Icc 1 t, if a ≤ vb τ then (1 : ℝ) else 0) / t) := by
  refine ⟨fun b hb => ?_, fun a ha => ?_⟩
  · unfold estSellOf
    congr 1
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    unfold chiSell
    have hiff : max (vs τ) (bid τ) ≤ b ↔ vs τ ≤ b := by
      rw [max_le_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hb τ hτ⟩⟩
    by_cases h : vs τ ≤ b
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  · unfold estBuyOf
    congr 1
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    unfold chiBuy
    have hiff : a ≤ min (vb τ) (ask τ) ↔ a ≤ vb τ := by
      rw [le_min_iff]; exact ⟨fun h => h.1, fun h => ⟨h, ha τ hτ⟩⟩
    by_cases h : a ≤ vb τ
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
