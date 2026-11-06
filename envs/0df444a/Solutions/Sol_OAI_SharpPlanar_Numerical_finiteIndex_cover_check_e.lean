-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_cover_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:27:20.554908+00:00
-- url     : https://prove2.me/submissions/8ee84411-e154-449e-bf82-28bdff2c2bf2

import Mathlib
import Definitions.Def_OAIQ098E007

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma finiteIndex_cover_check_e_oai : ∀ n : Fin 101, 0<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : FiniteIndex, (finiteIndex i).1.val=n.val ∧ (finiteIndex i).2=d := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_cover_check_e_oai := @OAI.SharpPlanar.Numerical.finiteIndex_cover_check_e_oai
