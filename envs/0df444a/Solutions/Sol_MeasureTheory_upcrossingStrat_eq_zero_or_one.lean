-- Prove2me | solution 1 for MeasureTheory.upcrossingStrat_eq_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T02:59:34.950512+00:00
-- url     : https://prove2.me/submissions/4f7b4f9f-b3f9-42b4-bc28-c76126c92cbb

import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}



theorem _root_.solution (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by
  rw [upcrossingStrat, ← Finset.indicator_biUnion_apply]
  · by_cases h : n ∈ ⋃ i ∈ Finset.range N,
        Set.Ico (lowerCrossingTime a b f N i ω) (upperCrossingTime a b f N (i + 1) ω)
    · right; rw [Set.indicator_of_mem h]; rfl
    · left; rw [Set.indicator_of_notMem h]
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  obtain hij' | hij' := lt_or_gt_of_ne hij
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    refine le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    refine le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))

