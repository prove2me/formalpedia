-- Prove2me | solution 1 for MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:59:18.618389+00:00
-- url     : https://prove2.me/submissions/811391df-9ad4-4ccb-817f-f8282498fb03

import Mathlib
import Definitions.Def_MazurN13_L0
import Definitions.Def_MazurN13_L4
import Theorems.Thm_HuangN13_N13RationalPointEndgame_affine_x_is_cuspidal_of_separated
import Theorems.Thm_HuangN13_N13ConstructedRationalPointTheorem_exists_separated_compatibleReduction


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof

theorem solution : ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 := by
  obtain ⟨D, separated⟩ := HuangN13.N13ConstructedRationalPointTheorem.exists_separated_compatibleReduction
  exact HuangN13.N13RationalPointEndgame.affine_x_is_cuspidal_of_separated D separated
