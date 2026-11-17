-- Prove2me | solution 1 for N25.GammaH25GL_isArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:51.140763+00:00
-- url     : https://prove2.me/submissions/7b26a519-4849-429d-bbf6-3cc452ef5333

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_level25_indices
import Definitions.Def_N25

set_option autoImplicit false

open scoped MatrixGroups

open Matrix.SpecialLinearGroup

namespace N25

theorem _root_.solution : GammaH25GL.IsArithmetic := by
  apply Subgroup.isArithmetic_iff_finiteIndex.mpr
  constructor
  rw [N25.level25_indices.1]
  decide

end N25
