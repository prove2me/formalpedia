-- Prove2me | solution 1 for LogStarBinPacking.claim_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:00:50.854524+00:00
-- url     : https://prove2.me/submissions/f491119c-e2da-47ed-9008-a091d6ecde7c

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_ThreeItem

open OAI.BinPackingGap

open LogStarBinPacking in
theorem solution (I : Instance) (b : ℕ) (hb : 1 ≤ b) (V : Type*) [Fintype V] [DecidableEq V]
    (h : V → ℚ) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (hV : I.n + b ≤ Fintype.card V) :
    Fintype.card (JItem I V b) = 3 * (Fintype.card V + b) ∧
    ∑ u : JItem I V b, ThreeItem.typeScore u = 0 ∧
    ∀ u : JItem I V b,
      1 / 3 - ε < ThreeItem.size I.size h ε u ∧ ThreeItem.size I.size h ε u < 1 / 3 + ε ∧
      1 / 4 < ThreeItem.size I.size h ε u ∧ ThreeItem.size I.size h ε u < 1 / 2 := by
  have hfN : fillerCount V I.n b + I.n + b = Fintype.card V := by
    unfold fillerCount; omega
  have hfZ : (fillerCount V I.n b : ℤ) = Fintype.card V - I.n - b := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hfN
    push_cast at this
    linarith
  refine ⟨?_, ?_, fun u => ?_⟩
  · rw [Fintype.card_congr ThreeItem.equivSum]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [← Equiv.sum_comp ThreeItem.equivSum.symm]
    simp only [Fintype.sum_sum_type]
    simp [ThreeItem.equivSum, ThreeItem.ofSum, ThreeItem.typeScore]
    linarith [hfZ]
  · have hl0 : 0 < ThreeItem.scale ε := lt_min (by linarith) (by norm_num)
    have hl1 : ThreeItem.scale ε ≤ 1 / 100 := min_le_right _ _
    have hl2 : ThreeItem.scale ε ≤ ε / 6 := min_le_left _ _
    obtain ⟨t0, t1⟩ := ThreeItem.typeScore_bounds u
    obtain ⟨l0, l1⟩ := ThreeItem.loadScore_bounds I.size h (fun i => (I.size_pos i).le)
      I.size_le_one h0 h1 u
    have t0' : (-4 : ℚ) ≤ ThreeItem.typeScore u := by exact_mod_cast t0
    have t1' : (ThreeItem.typeScore u : ℚ) ≤ 5 := by exact_mod_cast t1
    obtain ⟨X, hX⟩ : ∃ X, X = (ThreeItem.typeScore u : ℚ) + ThreeItem.loadScore I.size h u / 4 :=
      ⟨_, rfl⟩
    have hX0 : -(21 / 4 : ℚ) ≤ X := by rw [hX]; linarith
    have hX1 : X ≤ 21 / 4 := by rw [hX]; linarith
    have m1 := mul_nonneg hl0.le (by linarith : (0 : ℚ) ≤ 21 / 4 - X)
    have m2 := mul_nonneg hl0.le (by linarith : (0 : ℚ) ≤ X + 21 / 4)
    unfold ThreeItem.size
    rw [← hX]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
