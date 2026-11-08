-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:12:12.847+00:00
-- url     : https://prove2.me/submissions/00b2ae95-f876-4ce0-bd71-6542d5040cf0

import Mathlib
import Definitions.Def_OAIQ098G007

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
lemma finiteIndex_cover_check_g_oai : ∀ n : Fin 101, 0<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : FiniteIndex, (finiteIndex i).1.val=n.val ∧ (finiteIndex i).2=d := by decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g_oai := @OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g_oai
