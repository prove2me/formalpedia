-- Prove2me | solution 1 for Kyprianou.Ch04.predictableGridValueSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:52.655524+00:00
-- url     : https://prove2.me/submissions/330df0e3-13c0-4eae-89b6-882d801babc5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    (q : NNReal → NNReal) (a b : Nat → NNReal)
    (h0 : q 0 = 0)
    (hcell : ∀ k t, t ∈ Set.Ioc (a k) (b k) → q t = a k)
    (hcover : ∀ t, 0 < t → ∃ k, t ∈ Set.Ioc (a k) (b k))
    (g : NNReal → ENNReal) (t : NNReal) :
    g (q t) = max (({0} : Set NNReal).indicator (fun _ => g 0) t)
      (⨆ k, (Set.Ioc (a k) (b k)).indicator (fun _ => g (a k)) t) := by
  classical
  apply le_antisymm
  · by_cases ht : t = 0
    · subst t
      simpa [h0] using (le_max_left (g 0)
        (⨆ k, (Set.Ioc (a k) (b k)).indicator (fun _ => g (a k)) 0))
    · obtain ⟨k, hk⟩ := hcover t (pos_iff_ne_zero.mpr ht)
      rw [hcell k t hk]
      exact (le_iSup_of_le k (by simp [Set.indicator_of_mem hk])).trans (le_max_right _ _)
  · apply max_le
    · by_cases ht : t = 0 <;> simp [ht, h0, Set.indicator]
    · apply iSup_le
      intro k
      by_cases hk : t ∈ Set.Ioc (a k) (b k)
      · simp [Set.indicator_of_mem hk, hcell k t hk]
      · simp [Set.indicator_of_notMem hk]
