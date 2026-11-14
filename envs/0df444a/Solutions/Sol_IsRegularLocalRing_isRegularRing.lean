-- Prove2me | solution 1 for IsRegularLocalRing.isRegularRing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:45:30.752136+00:00
-- url     : https://prove2.me/submissions/eddbfce7-0ff3-421e-a73d-d28bc685bd40

import Mathlib
import Definitions.Def_RPLib_S4_JacDivisorsE

set_option autoImplicit false

theorem solution (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R := by
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact RamanujanPetersson.JacDivisors.isRegularLocalRing_localization p
