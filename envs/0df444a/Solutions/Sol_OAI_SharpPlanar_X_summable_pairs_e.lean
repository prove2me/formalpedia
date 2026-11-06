-- Prove2me | solution 1 for OAI.SharpPlanar.X_summable_pairs_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:17:38.061362+00:00
-- url     : https://prove2.me/submissions/d856ac90-e2db-459b-85b4-e3f2a7083dcb

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_X_summable_coord_e

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

theorem X_summable_pairs_e_oai (x : X) :
    Summable (fun n : Node => |x (n, false)| + |x (n, true)|) := by
  exact (X_summable_coord_e x false).add (X_summable_coord_e x true)


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.X_summable_pairs_e_oai := @OAI.SharpPlanar.X_summable_pairs_e_oai
