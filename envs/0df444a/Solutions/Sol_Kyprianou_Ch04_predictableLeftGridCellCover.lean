-- Prove2me | solution 1 for Kyprianou.Ch04.predictableLeftGridCellCover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:22.991991+00:00
-- url     : https://prove2.me/submissions/7f506365-ac8b-4dce-9326-3706d19f20d3

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    (n : Nat) (t : NNReal) (ht : 0 < t) :
    ∃ k : Nat, t ∈ Set.Ioc ((k : NNReal) / ((n : NNReal) + 1))
      (((k + 1 : Nat) : NNReal) / ((n : NNReal) + 1)) := by
  let c := Nat.ceil ((t : Real) * ((n : Real) + 1))
  have hd : 0 < (n : NNReal) + 1 := by positivity
  have ht' : 0 < (t : Real) := by exact_mod_cast ht
  have hc : 0 < c := Nat.ceil_pos.mpr (mul_pos ht' (by positivity))
  let k := c - 1
  have hk : k + 1 = c := by dsimp [k]; omega
  have hl : (k : Real) < (t : Real) * ((n : Real) + 1) :=
    Nat.lt_ceil.mp (by change k < c; omega)
  have hu : (t : Real) * ((n : Real) + 1) ≤ ((k + 1 : Nat) : Real) :=
    Nat.ceil_le.mp (by change c ≤ k + 1; omega)
  exact ⟨k, (div_lt_iff₀ hd).mpr (by exact_mod_cast hl),
    (le_div_iff₀ hd).mpr (by exact_mod_cast hu)⟩
