-- Prove2me | solution 1 for OAI.SharpPlanar.S_apply_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T09:14:08.640912+00:00
-- url     : https://prove2.me/submissions/04b24966-a110-440b-9e58-dbac753da5fb

import Mathlib
import Definitions.Def_OAIQ098G004

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma S_apply_g_oai (x : X) (ni : Node × Bool) : S x ni = Scoords x ni := rfl

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.S_apply_g_oai := @OAI.SharpPlanar.S_apply_g_oai
