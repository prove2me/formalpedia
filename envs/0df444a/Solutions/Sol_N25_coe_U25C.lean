-- Prove2me | solution 1 for N25.coe_U25C
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:57.604305+00:00
-- url     : https://prove2.me/submissions/90529085-e13a-4cca-9a74-001e8846331e

import Mathlib
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

namespace N25

/-- The modular unit `U25C K i` is the unit series `unitSeries25 K i`. -/
theorem _root_.solution (K : Type*) [Field K] (i : Fin 5) : (U25C K i).1 = unitSeries25 K i := by
  rw [U25C, dif_pos (unitSeries25_mem K i)]

end N25
