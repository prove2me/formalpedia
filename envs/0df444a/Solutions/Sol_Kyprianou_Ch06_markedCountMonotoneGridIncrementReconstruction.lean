-- Prove2me | solution 1 for Kyprianou.Ch06.markedCountMonotoneGridIncrementReconstruction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:14:02.407044+00:00
-- url     : https://prove2.me/submissions/202f6583-fc0a-47cf-9260-54ff5b0b1eb5

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_Kyprianou_Ch06_finiteMonotoneCountIncrementTelescoping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
set_option autoImplicit false

theorem solution
    (grid : Nat → NNReal) (hGrid : Monotone grid)
    (hGridZero : grid 0 = 0)
    (F : NNReal → Nat) (hF : Monotone F)
    (hFZero : F 0 = 0) (r : Nat) :
    F (grid r) =
      ∑ j ∈ Finset.range r, (F (grid (j + 1)) - F (grid j)) := by
  have hMono : Monotone (fun j : Nat => F (grid j)) :=
    hF.comp hGrid
  have hTel :=
    Kyprianou.Ch06.finiteMonotoneCountIncrementTelescoping
      (fun j : Nat => F (grid j)) hMono r
  simpa [hGridZero, hFZero] using hTel.symm
