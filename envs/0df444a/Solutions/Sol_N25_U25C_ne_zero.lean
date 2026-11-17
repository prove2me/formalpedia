-- Prove2me | solution 1 for N25.U25C_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:58.234601+00:00
-- url     : https://prove2.me/submissions/686855f1-7058-41bb-bcb4-5b88b4e6bb0d

import Mathlib
import Definitions.Def_N25_Units
import Theorems.Thm_N25_coe_U25C
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitSeries25_leadingCoeff
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

namespace N25

theorem _root_.solution (K : Type*) [Field K] (i : Fin 5) : U25C K i ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  rw [coe_U25C] at hv
  change unitSeries25 K i = 0 at hv
  have hc := unitSeries25_leadingCoeff K i
  rw [hv] at hc
  simpa using hc

end N25
