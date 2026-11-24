-- Prove2me | solution 1 for GlobalTheory.Lin.sum_primesIoc_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:44:01.168337+00:00
-- url     : https://prove2.me/submissions/dd66f650-6e69-47f7-b468-4bb5efaf977d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
namespace GlobalTheory.Lin
theorem _root_.solution (a : ℕ → ℂ) {x y t : ℝ} (ht : 0 ≤ t) (hty : t ≤ y) :
    ∑ p ∈ primesIoc x t, a p
      = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t := by
  have hs : primesIoc x t = (primesIoc x y).filter (fun p : ℕ => (p : ℝ) ≤ t) := by
    ext p
    simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨h1, h2.trans (Nat.floor_mono hty)⟩, hp⟩, (Nat.le_floor_iff ht).mp h2⟩
    · rintro ⟨⟨⟨h1, _⟩, hp⟩, h3⟩
      exact ⟨⟨h1, (Nat.le_floor_iff ht).mpr h3⟩, hp⟩
  rw [hs, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : (p : ℝ) ≤ t <;> simp [h]
end GlobalTheory.Lin
