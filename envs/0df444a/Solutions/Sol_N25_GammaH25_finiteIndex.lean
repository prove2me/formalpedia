-- Prove2me | solution 1 for N25.GammaH25_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:52.377862+00:00
-- url     : https://prove2.me/submissions/10bfdd85-3f6e-4d8e-9c2b-62e7425ffeb8

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_level25_indices
import Definitions.Def_N25

set_option autoImplicit false

open scoped MatrixGroups

open Matrix.SpecialLinearGroup

namespace N25

theorem _root_.solution : N25.Endgame.Γ25.FiniteIndex := by
  constructor
  rw [N25.level25_indices.1]
  decide

end N25
