-- Prove2me | solution 1 for LevyStochCalc.Probability.exists_lt_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:52:38.772701+00:00
-- url     : https://prove2.me/submissions/3c5fbdc0-f55d-40df-808b-e2f52713a441

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]



theorem _root_.solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < exitTime X (k : ℝ) ω := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) t)).exists_bound_of_continuousOn
    hX.continuousOn
  obtain ⟨K, hK⟩ := exists_nat_gt C
  refine ⟨K, fun k hk => ?_⟩
  have hkC : C < (k : ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hk)
  unfold exitTime
  split_ifs with hne
  · have hmem := csInf_exitSet_mem hX hne
    have hlt : t < sInf (exitSet X k ω) := by
      by_contra hle
      push_neg at hle
      have h1 := hC _ ⟨hmem.1, hle⟩
      have h2 := hmem.2
      linarith
    exact_mod_cast hlt
  · exact WithTop.coe_lt_top t
