-- Prove2me | solution 1 for OAI.SharpPlanar.X_summable_pairs_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:16:16.307447+00:00
-- url     : https://prove2.me/submissions/438c8a1a-90cf-4b3d-b83d-9d325239a076

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_X_summable_coord_g

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

theorem X_summable_pairs_g_oai (x : X) :
    Summable (fun n : Node => |x (n, false)| + |x (n, true)|) := by
  exact (X_summable_coord_g x false).add (X_summable_coord_g x true)


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.X_summable_pairs_g_oai := @OAI.SharpPlanar.X_summable_pairs_g_oai
