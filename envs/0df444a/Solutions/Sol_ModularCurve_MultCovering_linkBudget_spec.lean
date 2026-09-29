-- Prove2me | solution 1 for ModularCurve.MultCovering.linkBudget_spec
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a909f14a-a20b-54a0-9f71-464bddf1589b

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ModularCurve_MultCovering_exists_linkBudget
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_linkBudget_spec
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ i j, (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j ∈ A :=
  Nat.sInf_mem (ModularCurve.MultCovering.exists_linkBudget Φ s hs) A hA

end S_ModularCurve_MultCovering_linkBudget_spec
end P2MW
export P2MW.S_ModularCurve_MultCovering_linkBudget_spec (solution)
