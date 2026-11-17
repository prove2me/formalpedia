-- Prove2me | solution 1 for N25.U25C_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:01.709414+00:00
-- url     : https://prove2.me/submissions/51a1edfa-a6db-4057-bb99-54d0c23c96f8

import Mathlib
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_coe_U25C

set_option autoImplicit false

namespace N25

/-- The modular unit `U25C K i` is the unit series `unitSeries25 K i` with its membership proof. -/
theorem _root_.solution (K : Type*) [Field K] (i : Fin 5) :
    U25C K i = ⟨unitSeries25 K i, unitSeries25_mem K i⟩ := Subtype.ext (coe_U25C K i)

end N25
