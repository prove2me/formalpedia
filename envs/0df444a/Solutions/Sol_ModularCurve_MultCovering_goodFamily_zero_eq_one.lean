-- Prove2me | solution 1 for ModularCurve.MultCovering.goodFamily_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c354e8cc-5cc1-5cfd-85cc-1eed11ed4ec6

import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_goodFamily_zero_eq_one

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, (l : ℕ) = 0 → goodFamily Φ l = 1 :=
  Φ.t_zero

end S_ModularCurve_MultCovering_goodFamily_zero_eq_one
end P2MW
export P2MW.S_ModularCurve_MultCovering_goodFamily_zero_eq_one (solution)
