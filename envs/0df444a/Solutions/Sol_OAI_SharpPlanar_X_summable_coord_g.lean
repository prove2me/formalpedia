-- Prove2me | solution 1 for OAI.SharpPlanar.X_summable_coord_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:14:28.505282+00:00
-- url     : https://prove2.me/submissions/deabf602-653c-4250-adde-0e139d9ce369

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_X_summable_g

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

theorem X_summable_coord_g_oai (x : X) (i : Bool) : Summable (fun n : Node => |x (n, i)|) := by
  exact (X_summable_g x).comp_injective (fun _ _ hh => congrArg Prod.fst hh)


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.X_summable_coord_g_oai := @OAI.SharpPlanar.X_summable_coord_g_oai
