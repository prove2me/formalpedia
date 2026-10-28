-- Prove2me | solution 1 for ModelFreeBounds.Duality.cost_eq_max_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:12:29.256916+00:00
-- url     : https://prove2.me/submissions/aebadbc3-1613-4f87-a194-8264f717e39b

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

open ModelFreeBounds.Duality in
theorem solution {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (y : Fin m → ℝ) :
    IsGreatest ((fun q : Fin m → ℝ => ∑ j, y j * q j) '' M.box) (M.cost y) := by
  have hba := hM.bid_le_ask
  refine ⟨⟨fun j => if 0 ≤ y j then M.ask j else M.bid j, ?_, ?_⟩, ?_⟩
  · intro j _
    dsimp only
    split_ifs
    · exact ⟨hba j, le_refl _⟩
    · exact ⟨le_refl _, hba j⟩
  · unfold Market.cost
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    split_ifs with h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · have h' : y j < 0 := not_le.mp h
      rw [max_eq_right h'.le, max_eq_left (by linarith)]
      ring
  · rintro _ ⟨q, hq, rfl⟩
    unfold Market.cost
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨h1, h2⟩ := hq j (Set.mem_univ j)
    rcases le_total 0 (y j) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      nlinarith
    · rw [max_eq_right h, max_eq_left (by linarith)]
      nlinarith
