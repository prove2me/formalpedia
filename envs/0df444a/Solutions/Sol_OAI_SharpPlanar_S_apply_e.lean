-- Prove2me | solution 1 for OAI.SharpPlanar.S_apply_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T16:45:35.806438+00:00
-- url     : https://prove2.me/submissions/8794785b-0e4e-4fb9-878b-19a46e28aeb1

import Mathlib
import Definitions.Def_OAIQ098E004

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

lemma S_apply_e_oai (x : X) (ni : Node × Bool) : S x ni = Scoords x ni := rfl

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.S_apply_e_oai := @OAI.SharpPlanar.S_apply_e_oai
