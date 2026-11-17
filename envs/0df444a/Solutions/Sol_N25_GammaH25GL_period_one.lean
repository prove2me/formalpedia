-- Prove2me | solution 1 for N25.GammaH25GL_period_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:17.296956+00:00
-- url     : https://prove2.me/submissions/7ad68950-e89b-43aa-a25f-2f4bf954be2e

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Definitions.Def_N25

set_option autoImplicit false

open scoped MatrixGroups

open Matrix.SpecialLinearGroup

namespace N25

theorem _root_.solution : (1 : ℝ) ∈ GammaH25GL.strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem
    (ModularCurve.translation_mem_GammaH 25 N25.H25)]
  exact AddSubgroup.mem_zmultiples 1

end N25
