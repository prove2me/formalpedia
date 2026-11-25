-- Prove2me | solution 1 for Kyprianou.Ch04.predictableLeftGridClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:07:28.698677+00:00
-- url     : https://prove2.me/submissions/38e78ae9-50ec-4671-a4d5-0c150332b484

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_predictableLeftGridCellCeiling
import Theorems.Thm_Kyprianou_Ch04_predictableLeftGridCellCover
import Theorems.Thm_Kyprianou_Ch04_predictableLeftGridConvergesOfBounds
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution :
    ∃ (q : Nat → NNReal → NNReal) (a b : Nat → Nat → NNReal),
      (∀ n, q n 0 = 0) ∧
      (∀ n k t, t ∈ Set.Ioc (a n k) (b n k) → q n t = a n k) ∧
      (∀ n t, 0 < t → ∃ k, t ∈ Set.Ioc (a n k) (b n k)) ∧
      (∀ t : NNReal, 0 < t →
        Tendsto (fun n => (q n t : Real)) atTop
          (nhdsWithin (t : Real) (Set.Iio (t : Real)))) := by
  let a : Nat → Nat → NNReal := fun n k => (k : NNReal) / ((n : NNReal) + 1)
  let b : Nat → Nat → NNReal := fun n k => a n (k + 1)
  let q : Nat → NNReal → NNReal := fun n t =>
    a n (Nat.ceil ((t : Real) * ((n : Real) + 1)) - 1)
  have hcell : ∀ n k t, t ∈ Set.Ioc (a n k) (b n k) → q n t = a n k := by
    intro n k t ht
    simp [q, predictableLeftGridCellCeiling n k t ht]
  have hcover : ∀ n t, 0 < t → ∃ k, t ∈ Set.Ioc (a n k) (b n k) :=
    fun n t ht => predictableLeftGridCellCover n t ht
  refine ⟨q, a, b, fun n => by simp [q, a], hcell, hcover, ?_⟩
  intro t ht
  apply predictableLeftGridConvergesOfBounds (fun n => q n t) t
  intro n
  obtain ⟨k, hk⟩ := hcover n t ht
  rw [hcell n k t hk]
  refine ⟨by exact_mod_cast hk.1, ?_⟩
  have hu : (t : Real) ≤ ((k : Real) + 1) / ((n : Real) + 1) := by
    have hh : t ≤ (((k : NNReal) + 1) / ((n : NNReal) + 1)) := by
      simpa [b, a, Nat.cast_add, Nat.cast_one] using hk.2
    exact_mod_cast hh
  simpa [a, add_div] using hu
