-- Prove2me | solution 1 for Newton.killingForm_via_ad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:18:29.215291+00:00
-- url     : https://prove2.me/submissions/74eb9dfe-97f4-4338-a6a3-6e92c054ab2a

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
namespace Newton
theorem _root_.solution [DecidableEq (Fin N)] (A B : SuNAlgebra N) :
    killingForm A B = trace (A.matrix * B.matrix) := rfl
end Newton
