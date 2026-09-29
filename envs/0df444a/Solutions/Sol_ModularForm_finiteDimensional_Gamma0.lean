-- Prove2me | solution 1 for ModularForm.finiteDimensional_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/13a885b0-9cab-5e4b-8ff2-e9edc65180a1

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_finiteDimensional_Gamma0

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma0 N) k) := by
  exact ModularForm.finiteDimensional_of_isArithmetic _ k
end

end S_ModularForm_finiteDimensional_Gamma0
end P2MW
export P2MW.S_ModularForm_finiteDimensional_Gamma0 (solution)
