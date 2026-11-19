-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensity_factorAtTimes
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:07:29.043562+00:00
-- url     : https://prove2.me/submissions/0bc9a498-4123-4b35-9de9-a3771814e67d

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} (X : NNReal -> Omega -> Real)
    (beta k : Real) (s t : NNReal) (omega : Omega) :
    Kyprianou.Ch03.esscherDensity X beta k t omega =
      Kyprianou.Ch03.esscherDensity X beta k s omega *
        Real.exp (beta * (X t omega - X s omega) -
          k * ((t : Real) - (s : Real))) := by
  unfold Kyprianou.Ch03.esscherDensity
  rw [← Real.exp_add]
  congr 1
  ring
