-- Prove2me | solution 1 for NoHair.kerrNewman_einsteinMaxwell
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T05:55:00.157568+00:00
-- url     : https://prove2.me/submissions/072a91c6-5ab6-49f7-b76b-b766fa6733c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NoHair_kerrNewman
import Theorems.Thm_NoHair_kerrNewman_einstein
import Theorems.Thm_NoHair_kerrNewman_maxwell
import Theorems.Thm_NoHair_kerrNewman_field_closed

open scoped ContDiff Manifold BigOperators
open Set Matrix NoHair
set_option autoImplicit false

/-- The Einstein–Maxwell system is the conjunction of the Einstein equation, the source-free
Maxwell equation and closedness of `F`; each is supplied by one child lemma. -/
theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    EinsteinMaxwellAt (kerrNewmanMetric m a e) (kerrNewmanField a e) y :=
  ⟨kerrNewman_einstein m a e y hy, kerrNewman_maxwell m a e y hy, kerrNewman_field_closed a e y hy⟩
