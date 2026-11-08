-- Prove2me | solution 1 for OAI.SharpPlanar.scaleFactor_pos_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:26:22.858944+00:00
-- url     : https://prove2.me/submissions/ec1698b7-a270-40fe-bf76-61061de550db

import Mathlib
import Definitions.Def_OAIQ098G014
import Theorems.Thm_OAI_SharpPlanar_b_pos_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Dilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma scaleFactor_pos_g_oai : 0 < scaleFactor := inv_pos.mpr (Real.sqrt_pos.mpr b_pos_g)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.scaleFactor_pos_g_oai := @OAI.SharpPlanar.scaleFactor_pos_g_oai
