-- Prove2me | solution 1 for OAI.SharpPlanar.l1Finite_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T09:14:42.835332+00:00
-- url     : https://prove2.me/submissions/f6c726a1-e524-4701-995a-a1f9f0a0e81b

import Mathlib
import Definitions.Def_OAIQ098G004

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma l1Finite_norm_g_oai (x : L1Finite ι) : ‖x‖ = ∑ i, |x i| := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 x

end

end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.l1Finite_norm_g_oai.{u_1} := @OAI.SharpPlanar.l1Finite_norm_g_oai.{u_1}
