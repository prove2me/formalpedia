-- Prove2me | solution 1 for Kyprianou.Ch04.predictableLeftGridCellCeiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:11.339202+00:00
-- url     : https://prove2.me/submissions/748960f5-ad2a-40bf-9b9a-730919febe3d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    (n k : Nat) (t : NNReal)
    (ht : t ∈ Set.Ioc ((k : NNReal) / ((n : NNReal) + 1))
      (((k + 1 : Nat) : NNReal) / ((n : NNReal) + 1))) :
    Nat.ceil ((t : Real) * ((n : Real) + 1)) = k + 1 := by
  have hd : 0 < (n : NNReal) + 1 := by positivity
  have hl : (k : NNReal) < t * ((n : NNReal) + 1) := (div_lt_iff₀ hd).mp ht.1
  have hu : t * ((n : NNReal) + 1) ≤ ((k + 1 : Nat) : NNReal) := (le_div_iff₀ hd).mp ht.2
  have hl' : (k : Real) < (t : Real) * ((n : Real) + 1) := by exact_mod_cast hl
  have hu' : (t : Real) * ((n : Real) + 1) ≤ ((k + 1 : Nat) : Real) := by exact_mod_cast hu
  have h1 := Nat.lt_ceil.mpr hl'
  have h2 := Nat.ceil_le.mpr hu'
  omega
