-- Prove2me | solution 1 for LandauCriterion.landauLocal_eq_landau
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:59.399201+00:00
-- url     : https://prove2.me/submissions/c2598f28-b1ee-4a08-bda2-6b3c07aa50cd

import Mathlib
import Definitions.Def_LandauExplore_landauLocal
import Definitions.Def_LandauFunction_landau
open Finset LandauExplore LandauFunction

theorem solution (n : ℕ) : LandauExplore.landauLocal n = LandauFunction.landau n := rfl
